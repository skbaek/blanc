import Blanc.Weth10AllowanceArms

/-!
Balance-writing childless arms of the allowance-region transport.

Each arm discharges the `CompiledFrameAllowanceHandler` obligation for one
childless selector that writes only balance-region storage: the empty-data
`receive` path, `deposit`, `depositTo`, and the nonzero-recipient
`transfer` branch.  None of these touches an allowance slot and none has
an allowance event, so the frame's attribution stream is its own record
with `allowance = none`, and the singleton replay collapses to the entry
value at every tagged allowance key.  The storage side re-walks each
body's exact `SSTORE` keys: every written key is address-shaped, hence
disjoint from the tagged allowance region.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Local copies of the compiled body lines

`Weth10HolderFlowExecAccounting` keeps its per-selector line
decompositions private, so this module re-declares the ones it needs,
byte for byte. -/

private def mintCallerLine : Line :=
  [caller, sload, callvalue, add, caller, sstore, callvalue] ++
  mstoreAt 0 ++
  [caller, pushB256 0, pushB256 Blanc.transferEvent] ++
  logWith 2 0 1

private def transferSelectLine : Line := arg 0 ++ [iszero]

private def transferBalanceCheckLine : Line :=
  loadCallerBalanceAmount 1 ++ balanceTooSmall

private def transferNonzeroSuccessLine : Line :=
  debitLoadedBalance ++
  addressArg 0 ++ [dup 0, sload] ++ arg 1 ++
  [add, swap 0, sstore, caller] ++ arg 1 ++ addressArg 0 ++
  emitTransfer ++
  [pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

/-! ## The shared `mintCaller` storage walk

`receiveEther` and `deposit` are definitionally this body; its single
`SSTORE` writes the raw caller word, an address-shaped balance key. -/

private theorem mintCaller_allowanceKey {fs : List Func} {sevm : Sevm}
    {s r : Devm} {key : B256}
    (hkey : InRegion .allowance key)
    (run : Func.Run fs sevm s mintCaller r) :
    (Devm.getStor r sevm.currentTarget).get key =
      (Devm.getStor s sevm.currentTarget).get key := by
  unfold mintCaller at run
  rcases of_run_next run with ⟨s1, h_caller, run1⟩
  rcases of_run_next run1 with ⟨s2, h_sload, run2⟩
  rcases of_run_next run2 with ⟨s3, h_callvalue, run3⟩
  rcases of_run_next run3 with ⟨s4, h_add, run4⟩
  rcases of_run_next run4 with ⟨s5, h_caller2, run5⟩
  rcases of_run_next run5 with ⟨s6, h_sstore, run6⟩
  have hp1 : [sevm.caller.toB256] <<+ s1.stack :=
    prefix_of_push (of_run_caller h_caller) nil_pref
  rcases prefix_of_sload h_sload hp1 with ⟨callerBal, hp2, _⟩
  have hp3 : [sevm.value, callerBal] <<+ s3.stack :=
    prefix_of_push (of_run_callvalue h_callvalue) hp2
  have hp4 : [sevm.value + callerBal] <<+ s4.stack :=
    prefix_of_add h_add hp3
  have hp5 : [sevm.caller.toB256, sevm.value + callerBal] <<+ s5.stack :=
    prefix_of_push (of_run_caller h_caller2) hp4
  have h_set :
      Devm.getStor s6 sevm.currentTarget =
        (Devm.getStor s5 sevm.currentTarget).set sevm.caller.toB256
          (sevm.value + callerBal) :=
    sstore_getStor_set h_sstore hp5
  have hs_before : Devm.getStor s = Devm.getStor s5 := by
    rw [Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons h_caller Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons h_sload Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons h_callvalue Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons h_add Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons h_caller2 Line.Run.nil)]
  have hs_after : Devm.getStor s6 = Devm.getStor r := by
    apply Func.of_inv _ _ _ run6
    func_inv
  have hne : sevm.caller.toB256 ≠ key :=
    (allowanceRegion_ne_validAdr hkey ⟨sevm.caller, rfl⟩).symm
  rw [← congrFun hs_after sevm.currentTarget, h_set,
    Stor.get_set_ne _ hne _, ← congrFun hs_before sevm.currentTarget]

/-! ## The `receive` arm -/

/-- The empty-calldata receive arm is the childless mint body under the
main entry's calldatasize test, so an authentic committed frame
contributes no proper-descendant counted records; the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_receive`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hempty : frame.sevm.data.length.toB256 = 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  rcases frame.compiledMainCursorCounted context with ⟨mainCursor⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, hentryLine⟩
  have hflagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        entryBranchCursor.pre.stack := by
    rcases Line.of_run_cons hentryLine with
      ⟨afterSize, hsize, hrestSize⟩
    rcases Line.of_run_cons hrestSize with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero
      (prefix_of_push (of_run_calldatasize hsize) nil_pref)
  rw [hempty] at hflagPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at hflagPrefix
  rcases entryBranchCursor.selectBranchSucc (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨receiveCursor, _hstack⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (mintCallerLine +++ Func.last .stop) frame.post at receiveCursor
  rcases receiveCursor.peelChildlessLine
      (by simp [mintCallerLine, NinstIsChildless, Ninst.pushB256,
        mstoreAt, logWith]) with
    ⟨lastCursor, -⟩
  exact lastCursor.finishAttributionInner

/-- The receive arm transports the allowance region: the attribution
stream is the frame's own record alone, its event is `none` on the empty
calldata test, and the caller-key mint leaves every tagged allowance key
at its entry value. -/
theorem Exec.Frame.allowanceRegionEffect_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hempty : frame.sevm.data.length.toB256 = 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_receive context hempty
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hempty]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe, hinner,
      Exec.frameContribution_eq_cons dp ca frame []
        context.invocation hnotflash]
  rw [hstream]
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst hpc
      have hempty' : e.data.length.toB256 = 0 := hempty
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hcode : Devm.getCode pre ca = Devm.getCode post ca :=
        Exec.installedCodeEq run context.installed
      rcases exec_enters_weth10Receive_logs run context.invocation.2.2.2
          hempty' with
        ⟨mid, hstor0, _, _, _, _, _, hbody⟩
      have hmint : Func.Run ((weth10 dp).main :: weth10Aux) e mid
          mintCaller post := by
        simpa only [receiveEther] using hbody
      have hown : (CountedFrame.ofFrame dp ca
          (⟨0, e, pre, .ok post, run, committed⟩ : Exec.Frame)).allowance =
          none := by
        show frameAllowanceEvent e pre post = none
        simp [frameAllowanceEvent, hempty']
      refine ⟨fun key hkey => ?_, hcode⟩
      show (Devm.getStor post ca).get key =
        applyAllowanceLedger (Devm.getStor pre ca)
          [CountedFrame.ofFrame dp ca ⟨0, e, pre, .ok post, run, committed⟩]
          key
      rw [applyAllowanceLedger_singleton, hown]
      show (Devm.getStor post ca).get key = (Devm.getStor pre ca).get key
      rw [← htarget, mintCaller_allowanceKey hkey hmint,
        congrFun hstor0 e.currentTarget]

/-! ## The `deposit` arm -/

/-- The payable `deposit` dispatch body is the same childless mint body as
the receive arm, so an authentic committed frame contributes no
proper-descendant counted records; the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_deposit`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "deposit" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm, deposit) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmem with
    ⟨bodyCursor⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (mintCallerLine +++ Func.last .stop) frame.post at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (by simp [mintCallerLine, NinstIsChildless, Ninst.pushB256,
        mstoreAt, logWith]) with
    ⟨lastCursor, -⟩
  exact lastCursor.finishAttributionInner

/-- `deposit` transports the allowance region: the attribution stream is
the frame's own record alone, its event is `none` on every selector test,
and the caller-key mint leaves every tagged allowance key at its entry
value. -/
theorem Exec.Frame.allowanceRegionEffect_of_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "deposit" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_deposit context hselector hnonempty
  have hsel : Sevm.selector frame.sevm = depositSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, depositSelector_ne_flashLoanSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe, hinner,
      Exec.frameContribution_eq_cons dp ca frame []
        context.invocation hnotflash]
  rw [hstream]
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst hpc
      have hselE : Sevm.selector e = depositSelector := hselector
      have hne0 : e.data.length.toB256 ≠ 0 := hnonempty
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hcode : Devm.getCode pre ca = Devm.getCode post ca :=
        Exec.installedCodeEq run context.installed
      have hmem : (selector "deposit" [], deposit) ∈ weth10Funcs dp := by
        simp [weth10Funcs]
      rcases exec_enters_weth10Selector_logs run context.invocation.2.2.2
          hselector hne0 hmem with
        ⟨mid, hstor0, _, _, _, _, _, hbody⟩
      have hmint : Func.Run ((weth10 dp).main :: weth10Aux) e mid
          mintCaller post := by
        simpa only [deposit] using hbody
      have hown : (CountedFrame.ofFrame dp ca
          (⟨0, e, pre, .ok post, run, committed⟩ : Exec.Frame)).allowance =
          none := by
        show frameAllowanceEvent e pre post = none
        simp [frameAllowanceEvent, hne0, hselE,
          depositSelector_ne_approveSelector,
          depositSelector_ne_approveAndCallSelector,
          depositSelector_ne_permitSelector,
          depositSelector_ne_transferFromSelector,
          depositSelector_ne_withdrawFromSelector,
          depositSelector_ne_flashLoanSelector,
          depositSelector_ne_allowanceSelector]
      refine ⟨fun key hkey => ?_, hcode⟩
      show (Devm.getStor post ca).get key =
        applyAllowanceLedger (Devm.getStor pre ca)
          [CountedFrame.ofFrame dp ca ⟨0, e, pre, .ok post, run, committed⟩]
          key
      rw [applyAllowanceLedger_singleton, hown]
      show (Devm.getStor post ca).get key = (Devm.getStor pre ca).get key
      rw [← htarget, mintCaller_allowanceKey hkey hmint,
        congrFun hstor0 e.currentTarget]

/-! ## The `depositTo` arm -/

/-- The payable `depositTo` dispatch body is childless through its
terminal stop, so an authentic committed frame contributes no
proper-descendant counted records; the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_depositTo`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "depositTo" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm, depositTo) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmem with
    ⟨bodyCursor⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (mintToPrefix +++ Func.last .stop) frame.post at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (by simp [mintToPrefix, addressArg, arg, cdl,
        normalizeAddress, pushAddressMask, NinstIsChildless,
        Ninst.pushB256, mstoreAt, logWith]) with
    ⟨lastCursor, -⟩
  exact lastCursor.finishAttributionInner

/-- `depositTo` transports the allowance region: the attribution stream is
the frame's own record alone, its event is `none` on every selector test,
and the normalized-key mint leaves every tagged allowance key at its
entry value. -/
theorem Exec.Frame.allowanceRegionEffect_of_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "depositTo" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_depositTo context hselector hnonempty
  have hsel : Sevm.selector frame.sevm = depositToSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, depositToSelector_ne_flashLoanSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe, hinner,
      Exec.frameContribution_eq_cons dp ca frame []
        context.invocation hnotflash]
  rw [hstream]
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst hpc
      have hselE : Sevm.selector e = depositToSelector := hselector
      have hne0 : e.data.length.toB256 ≠ 0 := hnonempty
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hcode : Devm.getCode pre ca = Devm.getCode post ca :=
        Exec.installedCodeEq run context.installed
      have heffect := depositTo_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2 hselector
        hne0
      have hstor := heffect.1
      have hvalid : ValidAdr (normalizedAddressArg e 0) :=
        normalizedAddress_valid (Sevm.argWord e 0)
      have hown : (CountedFrame.ofFrame dp ca
          (⟨0, e, pre, .ok post, run, committed⟩ : Exec.Frame)).allowance =
          none := by
        show frameAllowanceEvent e pre post = none
        simp [frameAllowanceEvent, hne0, hselE,
          depositToSelector_ne_approveSelector,
          depositToSelector_ne_approveAndCallSelector,
          depositToSelector_ne_permitSelector,
          depositToSelector_ne_transferFromSelector,
          depositToSelector_ne_withdrawFromSelector,
          depositToSelector_ne_flashLoanSelector,
          depositToSelector_ne_allowanceSelector]
      refine ⟨fun key hkey => ?_, hcode⟩
      show (Devm.getStor post ca).get key =
        applyAllowanceLedger (Devm.getStor pre ca)
          [CountedFrame.ofFrame dp ca ⟨0, e, pre, .ok post, run, committed⟩]
          key
      rw [applyAllowanceLedger_singleton, hown]
      show (Devm.getStor post ca).get key = (Devm.getStor pre ca).get key
      rw [← htarget, hstor,
        Stor.get_set_ne _ ((allowanceRegion_ne_validAdr hkey hvalid).symm) _]

/-! ## The `transfer` nonzero-recipient arm -/

/-- The nonzero-recipient `transfer` branch performs exactly two `SSTORE`s,
at the raw caller word and at the normalized address-argument word — both
address-shaped balance keys — so every tagged allowance key keeps its
entry value. -/
private theorem transferNonzeroThen_allowanceKey (dp : DeployParams)
    {e : Sevm} {s r : Devm} {key : B256}
    (hkey : InRegion .allowance key)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (transferNonzeroThen returnTrue) r) :
    (Devm.getStor r e.currentTarget).get key =
      (Devm.getStor s e.currentTarget).get key := by
  simp only [transferNonzeroThen] at run
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, _hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 : (balance <? Sevm.argWord e 1) :: balance ::
      Sevm.argWord e 1 :: e.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  rcases of_run_branch_call_revWith
      (transferBalanceError_lookup dp) run2 with
    ⟨s3, hguardPop, run3⟩
  have hguardStack := hguardPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hguardStack
  rw [hguardStack] at hp2
  have hflag : (balance <? Sevm.argWord e 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  rw [hflag] at hp2
  have hp3 : balance :: Sevm.argWord e 1 :: e.caller.toB256 ::
      [] <<+ s3.stack := cons_pref_cons_inv hp2
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  unfold debitLoadedBalance at hdebit
  rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
  have hpD1 : (balance - Sevm.argWord e 1) :: e.caller.toB256 :: [] <<+
      d1.stack := prefix_of_sub hsub hp3
  rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
  have hswapCoreD : Stack.Swap (0 : Fin 16).val
      [balance - Sevm.argWord e 1, e.caller.toB256]
      [e.caller.toB256, balance - Sevm.argWord e 1] :=
    Stack.swapCore_zero
  have hpD2 : e.caller.toB256 :: (balance - Sevm.argWord e 1) :: [] <<+
      d2.stack :=
    Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
  rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
  cases hnilD
  have hsetDebit : Devm.getStor s4 e.currentTarget =
      (Devm.getStor d2 e.currentTarget).set e.caller.toB256
        (balance - Sevm.argWord e 1) :=
    sstore_getStor_set hstore hpD2
  rcases of_run_prepend (addressArg 0 ++ [dup 0, sload] ++ arg 1 ++
      [add, swap 0, sstore]) _ run4 with
    ⟨s5, hcredit, run5⟩
  rcases of_run_append (addressArg 0) hcredit with ⟨c1, haddr, hcredit1⟩
  have hpC1 : ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+
      c1.stack := prefix_of_addressArg nil_pref haddr
  rcases of_run_append [dup 0] hcredit1 with ⟨c2, hdupLine, hcredit2⟩
  rcases Line.of_run_cons hdupLine with ⟨c2', hdup, hnil2⟩
  cases hnil2
  have hpC2 : ((~~~ addressMask) &&& Sevm.argWord e 0) ::
      ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c2.stack :=
    prefix_of_dup_val hdup (by show_nth) hpC1
  rcases of_run_append [sload] hcredit2 with ⟨c3, hloadLine, hcredit3⟩
  rcases Line.of_run_cons hloadLine with ⟨c3', hloadN, hnil3⟩
  cases hnil3
  rcases prefix_of_sload hloadN hpC2 with ⟨toBal, hpC3, _⟩
  rcases of_run_append (arg 1) hcredit3 with ⟨c4, hamount, hcredit4⟩
  have hpC4 : Sevm.argWord e 1 :: toBal ::
      ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c4.stack :=
    prefix_of_arg hpC3 hamount
  rcases Line.of_run_cons hcredit4 with ⟨c5, haddN, hcredit5⟩
  have hpC5 : (Sevm.argWord e 1 + toBal) ::
      ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c5.stack :=
    prefix_of_add haddN hpC4
  rcases Line.of_run_cons hcredit5 with ⟨c6, hswapN, hcredit6⟩
  have hswapCoreC : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 1 + toBal, (~~~ addressMask) &&& Sevm.argWord e 0]
      [(~~~ addressMask) &&& Sevm.argWord e 0, Sevm.argWord e 1 + toBal] :=
    Stack.swapCore_zero
  have hpC6 : ((~~~ addressMask) &&& Sevm.argWord e 0) ::
      (Sevm.argWord e 1 + toBal) :: [] <<+ c6.stack :=
    Stack.prefix_of_swap hswapCoreC (of_run_swap hswapN) hpC5
  rcases Line.of_run_cons hcredit6 with ⟨c7, hstoreN, hnil7⟩
  cases hnil7
  have hsetCredit : Devm.getStor s5 e.currentTarget =
      (Devm.getStor c6 e.currentTarget).set
        ((~~~ addressMask) &&& Sevm.argWord e 0)
        (Sevm.argWord e 1 + toBal) :=
    sstore_getStor_set hstoreN hpC6
  have hsInv1 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hguardPop))
  have hsInv2 : Devm.getStor s3 = Devm.getStor d2 :=
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hsub Line.Run.nil)).trans
      (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil))
  have hsInv3 : Devm.getStor s4 = Devm.getStor c6 := by
    rw [Line.of_inv Devm.getStor (by line_inv) haddr,
      Line.of_inv Devm.getStor (by line_inv) hdupLine,
      Line.of_inv Devm.getStor (by line_inv) hloadLine,
      Line.of_inv Devm.getStor (by line_inv) hamount,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons haddN Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswapN Line.Run.nil)]
  have hsInv4 : Devm.getStor s5 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) run5
  have hneCaller : e.caller.toB256 ≠ key :=
    (allowanceRegion_ne_validAdr hkey ⟨e.caller, rfl⟩).symm
  have hneNorm : ((~~~ addressMask) &&& Sevm.argWord e 0) ≠ key :=
    (allowanceRegion_ne_validAdr hkey
      (normalizedAddress_valid (Sevm.argWord e 0))).symm
  rw [← congrFun hsInv4 e.currentTarget, hsetCredit,
    Stor.get_set_ne _ hneNorm _, ← congrFun hsInv3 e.currentTarget,
    hsetDebit, Stor.get_set_ne _ hneCaller _,
    ← congrFun hsInv2 e.currentTarget, ← congrFun hsInv1 e.currentTarget]

/-- A successful ordinary `transfer` with a nonzero raw recipient word
takes the call-free branch, whose only inner conditional tail-calls a
fixed reverter; the committed frame therefore contributes no
proper-descendant counted records.  The counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_transferNonzero`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_transferNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "transfer" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transfer) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmem with
    ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨transferCursor⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferSelectLine +++
      (transferZeroThen returnTrue <?> transferNonzeroThen returnTrue))
    frame.post at transferCursor
  rcases transferCursor.peelChildlessLine
      (by simp [transferSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 0 =? 0] <<+
        targetBranchCursor.pre.stack := by
    unfold transferSelectLine at htargetLine
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 0 =? 0) = 0 := by
    simp [B256.eqCheck, hto]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchZero htargetPrefix with
    ⟨nonzeroCursor, _hnonzeroStack⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferBalanceCheckLine +++
      ((.call transferBalanceErrorSlot) <?>
        (transferNonzeroSuccessLine +++ Func.last .ret)))
    frame.post at nonzeroCursor
  rcases nonzeroCursor.peelChildlessLine
      (by simp [transferBalanceCheckLine, loadCallerBalanceAmount,
        balanceTooSmall, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨balanceBranchCursor, hbalanceLine⟩
  rcases of_run_append (loadCallerBalanceAmount 1) hbalanceLine with
    ⟨midState, hload, hguardRun⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, _hbalance, hpLoad⟩
  have hpFlag := prefix_of_balanceTooSmall hpLoad hguardRun
  by_cases hflag : (balance <? Sevm.argWord frame.sevm 1) = 0
  · rw [hflag] at hpFlag
    rcases balanceBranchCursor.selectBranchZero hpFlag with
      ⟨successCursor, _hsuccessStack⟩
    rcases successCursor.peelChildlessLine
        (by simp [transferNonzeroSuccessLine, debitLoadedBalance,
          addressArg, arg, cdl, normalizeAddress, pushAddressMask,
          emitTransfer, Blanc.transferFromLog, NinstIsChildless,
          Ninst.pushB256, mstoreAt, logWith, pushList]) with
      ⟨lastCursor, -⟩
    exact lastCursor.finishAttributionInner
  · exfalso
    rcases balanceBranchCursor.selectBranchSucc hflag hpFlag with
      ⟨errorCursor, -⟩
    have hrun := Func.Run.of_runCompiled errorCursor.run
    cases hrun with
    | call hget _hburn hbody =>
        rw [transferBalanceError_lookup dp] at hget
        cases Option.some.inj hget
        exact Func.not_run_revWith hbody

/-- Nonzero-recipient `transfer` transports the allowance region: the
attribution stream is the frame's own record alone, its event is `none`
on every selector test, and the two balance-key writes leave every tagged
allowance key at its entry value. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "transfer" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_transferNonzero context hselector
      hnonempty hto
  have hsel : Sevm.selector frame.sevm = transferSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, transferSelector_ne_flashLoanSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe, hinner,
      Exec.frameContribution_eq_cons dp ca frame []
        context.invocation hnotflash]
  rw [hstream]
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst hpc
      have hselE : Sevm.selector e = transferSelector := hselector
      have hne0 : e.data.length.toB256 ≠ 0 := hnonempty
      have hto' : Sevm.argWord e 0 ≠ 0 := hto
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hcode : Devm.getCode pre ca = Devm.getCode post ca :=
        Exec.installedCodeEq run context.installed
      have hmem : (selector "transfer" [.address, .uint256],
          nonpayable transfer) ∈ weth10Funcs dp := by
        simp [weth10Funcs]
      rcases exec_enters_weth10Nonpayable_logs run context.invocation.2.2.2
          hselector hne0 hmem with
        ⟨mid, _hvalue, hstor0, _, _, _, _, _, hbody⟩
      simp only [transfer, transferThen] at hbody
      rcases of_run_prepend (arg 0) _ hbody with ⟨s1, harg, run1⟩
      have hp1 : Sevm.argWord e 0 :: [] <<+ s1.stack :=
        prefix_of_arg nil_pref harg
      rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
      have hp2 : (Sevm.argWord e 0 =? 0) :: [] <<+ s2.stack :=
        prefix_of_iszero hiszero hp1
      rcases of_run_branch run2 with
          ⟨s3, hpop, hnonzero⟩ |
          ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
      · have hstorEntry : Devm.getStor mid = Devm.getStor s3 :=
          (Line.of_inv Devm.getStor (by line_inv) harg).trans
            ((Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons hiszero Line.Run.nil)).trans
              (PopBurn.Inv.inv hpop))
        have hown : (CountedFrame.ofFrame dp ca
            (⟨0, e, pre, .ok post, run, committed⟩ :
              Exec.Frame)).allowance = none := by
          show frameAllowanceEvent e pre post = none
          simp [frameAllowanceEvent, hne0, hselE,
            transferSelector_ne_approveSelector,
            transferSelector_ne_approveAndCallSelector,
            transferSelector_ne_permitSelector,
            transferSelector_ne_transferFromSelector,
            transferSelector_ne_withdrawFromSelector,
            transferSelector_ne_flashLoanSelector,
            transferSelector_ne_allowanceSelector]
        refine ⟨fun key hkey => ?_, hcode⟩
        show (Devm.getStor post ca).get key =
          applyAllowanceLedger (Devm.getStor pre ca)
            [CountedFrame.ofFrame dp ca
              ⟨0, e, pre, .ok post, run, committed⟩]
            key
        rw [applyAllowanceLedger_singleton, hown]
        show (Devm.getStor post ca).get key =
          (Devm.getStor pre ca).get key
        rw [← htarget, transferNonzeroThen_allowanceKey dp hkey hnonzero,
          ← congrFun hstorEntry e.currentTarget,
          congrFun hstor0 e.currentTarget]
      · have hpopStack := hpop.stack
        simp only [Stack.Pop, Split, List.nil_append,
          List.cons_append] at hpopStack
        rw [hpopStack] at hp2
        have hflag : (Sevm.argWord e 0 =? 0) = w :=
          pref_head_unique hp2 (pref_append [w] s3.stack)
        have hargZero : Sevm.argWord e 0 = 0 := by
          by_contra hne
          rw [B256.eqCheck, if_neg hne] at hflag
          exact hnz hflag.symm
        exact absurd hargZero hto'

end Weth10

end Blanc
