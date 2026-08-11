import Blanc.Weth10AllowanceArmsBalance

/-!
The delegated `transferFrom` nonzero-recipient arm of the allowance-region
transport.

`transferFrom` is `spendCallerAllowanceThen 2 transferFromCoreSlot`: the
allowance wrapper forks on the self-bypass test and on an infinite
allowance before an internal table jump into `transferFromCore`.  Every
committed nonzero-recipient path is childless: the `.call` slots crossed
are internal table jumps, and the reverter alternatives cannot commit, so
the frame's attribution stream is its own record.  The storage side
replays the wrapper's exact `CallerAllowanceOutcome` fork — self-bypass
and infinite allowance write nothing, the finite spend writes exactly the
tagged runtime key — and re-walks the core's two balance-key `SSTORE`s at
the `Func.Run` altitude, because the packaged core effect is
`Stor.rest`-projected and says nothing about tagged allowance keys.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Local copies of the compiled body lines

`Weth10HolderFlowExecAccounting` and `Weth10HolderFlowCompiled` keep their
per-selector line decompositions private, so this module re-declares the
ones it needs, byte for byte. -/

private def transferFromSelectLine : Line := arg 1 ++ [iszero]

private def transferFromBalanceCheckLine : Line :=
  loadArgBalanceAmount 0 2 ++ balanceTooSmall

private def transferFromNonzeroSuccessLine : Line :=
  debitLoadedBalance ++
  addressArg 1 ++ [dup 0, sload] ++ arg 2 ++ [add, swap 0, sstore] ++
  addressArg 0 ++ arg 2 ++ addressArg 1 ++ emitTransfer ++
  [pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

/-! ## The counted allowance-wrapper crossing -/

/-- Follow the actual successful allowance wrapper to its internal core
while preserving the empty counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.enterSpendCallerAllowanceThen`.  Every wrapper
instruction is childless; the only alternate internal call is the fixed
allowance reverter, which cannot lead to the committed final state. -/
private theorem Exec.Frame.CountedCursor.enterSpendCallerAllowanceThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {amount : B256} {nextSlot : Nat}
    {final : Devm}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux))
      (spendCallerAllowanceThen amount nextSlot) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (hallowanceError :
      (f₀ :: aux)[allowanceErrorSlot]? =
        some (Func.revWith "WETH: request exceeds allowance")) :
    ∃ body,
      (f₀ :: aux)[nextSlot]? = some body ∧
      Nonempty (frame.CountedCursor dp ca (f₀ :: aux)
        (table 0 (f₀ :: aux)) body final) := by
  unfold spendCallerAllowanceThen at cursor
  rcases cursor.peelChildlessLine
      (line := arg 0 ++ [Ninst.caller, Ninst.eq])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨callerBranchCursor, -⟩
  rcases callerBranchCursor.selectBranchSplit with hallowance | hdirect
  · rcases hallowance with ⟨allowanceCursor⟩
    rcases allowanceCursor.peelChildlessLine
        (line := arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
          allowanceKeyFromMemory ++
          [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ isMax)
        (by simp [arg, cdl, mstoreAt, allowanceKeyFromMemory, pushList,
          isMax, NinstIsChildless, Ninst.pushB256]) with
      ⟨maxBranchCursor, -⟩
    rcases maxBranchCursor.selectBranchSplit with hfinite | hmax
    · rcases hfinite with ⟨finiteCursor⟩
      rcases finiteCursor.peelChildlessLine
          (line := arg amount ++ [Ninst.swap 0] ++ balanceTooSmall)
          (by simp [arg, cdl, balanceTooSmall, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨spendBranchCursor, -⟩
      rcases spendBranchCursor.selectBranchSplit with hsuccess | herror
      · rcases hsuccess with ⟨successCursor⟩
        rcases successCursor.peelChildlessLine
            (line := [Ninst.sub, Ninst.dup 0, Ninst.swap 1,
                Ninst.sstore] ++
              arg 0 ++ [Ninst.swap 0, Ninst.caller] ++ emitApproval ++
              [Ninst.pop, Ninst.pop])
            (by simp [arg, cdl, emitApproval, mstoreAt,
              logWith, NinstIsChildless, Ninst.pushB256]) with
          ⟨coreCallCursor, -⟩
        exact coreCallCursor.enterCall hcode
      · rcases herror with ⟨errorCursor⟩
        have hrun := Func.Run.of_runCompiled errorCursor.run
        cases hrun with
        | call hget _hburn hbody =>
            rw [hallowanceError] at hget
            cases Option.some.inj hget
            exact absurd hbody Func.not_run_revWith
    · rcases hmax with ⟨maxCursor⟩
      rcases maxCursor.peelChildlessLine
          (line := [Ninst.pop, Ninst.pop])
          (by simp [NinstIsChildless]) with
        ⟨coreCallCursor, -⟩
      exact coreCallCursor.enterCall hcode
  · rcases hdirect with ⟨directCursor⟩
    exact directCursor.enterCall hcode

/-! ## The core's storage effect on the allowance region

The packaged `TransferFromCoreSuccessEffect` states the core's balance
movement at the `Stor.rest` altitude, which says nothing about tagged
allowance keys, so the core body is re-walked here at the `Func.Run`
altitude: its only two `SSTORE`s hit the normalized source and recipient
words, both address-shaped balance keys. -/

/-- The nonzero-recipient `transferFrom` core performs exactly two
`SSTORE`s, at the normalized source word and at the normalized recipient
word — both address-shaped balance keys — so every tagged allowance key
keeps its entry value. -/
private theorem transferFromNonzero_allowanceKey (dp : DeployParams)
    {e : Sevm} {s r : Devm} {key : B256}
    (hkey : InRegion .allowance key)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      transferFromNonzero r) :
    (Devm.getStor r e.currentTarget).get key =
      (Devm.getStor s e.currentTarget).get key := by
  simp only [transferFromNonzero] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, owner, howner, _hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 : (balance <? Sevm.argWord e 2) :: balance ::
      Sevm.argWord e 2 :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  rcases of_run_branch_call_revWith
      (transferBalanceError_lookup dp) run2 with
    ⟨s3, hguardPop, run3⟩
  have hguardStack := hguardPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hguardStack
  rw [hguardStack] at hp2
  have hflag : (balance <? Sevm.argWord e 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  rw [hflag] at hp2
  have hp3 : balance :: Sevm.argWord e 2 :: owner ::
      [] <<+ s3.stack := cons_pref_cons_inv hp2
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  unfold debitLoadedBalance at hdebit
  rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
  have hpD1 : (balance - Sevm.argWord e 2) :: owner :: [] <<+
      d1.stack := prefix_of_sub hsub hp3
  rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
  have hswapCoreD : Stack.Swap (0 : Fin 16).val
      [balance - Sevm.argWord e 2, owner]
      [owner, balance - Sevm.argWord e 2] :=
    Stack.swapCore_zero
  have hpD2 : owner :: (balance - Sevm.argWord e 2) :: [] <<+
      d2.stack :=
    Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
  rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
  cases hnilD
  have hsetDebit : Devm.getStor s4 e.currentTarget =
      (Devm.getStor d2 e.currentTarget).set owner
        (balance - Sevm.argWord e 2) :=
    sstore_getStor_set hstore hpD2
  rcases of_run_prepend (addressArg 1 ++ [dup 0, sload] ++ arg 2 ++
      [add, swap 0, sstore]) _ run4 with
    ⟨s5, hcredit, run5⟩
  rcases of_run_append (addressArg 1) hcredit with ⟨c1, haddr, hcredit1⟩
  have hpC1 : ((~~~ addressMask) &&& Sevm.argWord e 1) :: [] <<+
      c1.stack := prefix_of_addressArg nil_pref haddr
  rcases of_run_append [dup 0] hcredit1 with ⟨c2, hdupLine, hcredit2⟩
  rcases Line.of_run_cons hdupLine with ⟨c2', hdup, hnil2⟩
  cases hnil2
  have hpC2 : ((~~~ addressMask) &&& Sevm.argWord e 1) ::
      ((~~~ addressMask) &&& Sevm.argWord e 1) :: [] <<+ c2.stack :=
    prefix_of_dup_val hdup (by show_nth) hpC1
  rcases of_run_append [sload] hcredit2 with ⟨c3, hloadLine, hcredit3⟩
  rcases Line.of_run_cons hloadLine with ⟨c3', hloadN, hnil3⟩
  cases hnil3
  rcases prefix_of_sload hloadN hpC2 with ⟨toBal, hpC3, _⟩
  rcases of_run_append (arg 2) hcredit3 with ⟨c4, hamount, hcredit4⟩
  have hpC4 : Sevm.argWord e 2 :: toBal ::
      ((~~~ addressMask) &&& Sevm.argWord e 1) :: [] <<+ c4.stack :=
    prefix_of_arg hpC3 hamount
  rcases Line.of_run_cons hcredit4 with ⟨c5, haddN, hcredit5⟩
  have hpC5 : (Sevm.argWord e 2 + toBal) ::
      ((~~~ addressMask) &&& Sevm.argWord e 1) :: [] <<+ c5.stack :=
    prefix_of_add haddN hpC4
  rcases Line.of_run_cons hcredit5 with ⟨c6, hswapN, hcredit6⟩
  have hswapCoreC : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 2 + toBal, (~~~ addressMask) &&& Sevm.argWord e 1]
      [(~~~ addressMask) &&& Sevm.argWord e 1, Sevm.argWord e 2 + toBal] :=
    Stack.swapCore_zero
  have hpC6 : ((~~~ addressMask) &&& Sevm.argWord e 1) ::
      (Sevm.argWord e 2 + toBal) :: [] <<+ c6.stack :=
    Stack.prefix_of_swap hswapCoreC (of_run_swap hswapN) hpC5
  rcases Line.of_run_cons hcredit6 with ⟨c7, hstoreN, hnil7⟩
  cases hnil7
  have hsetCredit : Devm.getStor s5 e.currentTarget =
      (Devm.getStor c6 e.currentTarget).set
        ((~~~ addressMask) &&& Sevm.argWord e 1)
        (Sevm.argWord e 2 + toBal) :=
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
  have hneOwner : owner ≠ key := by
    refine (allowanceRegion_ne_validAdr hkey ?_).symm
    rw [howner]
    exact normalizedAddress_valid (Sevm.argWord e 0)
  have hneNorm : ((~~~ addressMask) &&& Sevm.argWord e 1) ≠ key :=
    (allowanceRegion_ne_validAdr hkey
      (normalizedAddress_valid (Sevm.argWord e 1))).symm
  rw [← congrFun hsInv4 e.currentTarget, hsetCredit,
    Stor.get_set_ne _ hneNorm _, ← congrFun hsInv3 e.currentTarget,
    hsetDebit, Stor.get_set_ne _ hneOwner _,
    ← congrFun hsInv2 e.currentTarget, ← congrFun hsInv1 e.currentTarget]

/-- The `transferFrom` core with a nonzero raw recipient word takes the
storage-transfer branch, whose writes are balance-region only. -/
private theorem transferFromCore_allowanceKey (dp : DeployParams)
    {e : Sevm} {s r : Devm} {key : B256}
    (hkey : InRegion .allowance key)
    (hto : Sevm.argWord e 1 ≠ 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      transferFromCore r) :
    (Devm.getStor r e.currentTarget).get key =
      (Devm.getStor s e.currentTarget).get key := by
  simp only [transferFromCore] at run
  rcases of_run_prepend (arg 1) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e 1 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord e 1 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have hstorEntry : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
          (PopBurn.Inv.inv hpop))
    rw [transferFromNonzero_allowanceKey dp hkey hnonzero,
      ← congrFun hstorEntry e.currentTarget]
  · have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hp2
    have hflag : (Sevm.argWord e 1 =? 0) = w :=
      pref_head_unique hp2 (pref_append [w] s3.stack)
    have hargZero : Sevm.argWord e 1 = 0 := by
      by_contra hne
      rw [B256.eqCheck, if_neg hne] at hflag
      exact hnz hflag.symm
    exact absurd hargZero hto

/-! ## The `transferFrom` nonzero-recipient arm -/

/-- A successful delegated `transferFrom` with a nonzero raw recipient
word crosses only childless instructions and internal table jumps, and
its reverter alternatives cannot be the retained frame's committed
continuation; the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_transferFromNonzero`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_transferFromNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "transferFrom" [.address, .address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transferFrom) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmem with
    ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨spendCursor⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 transferFromCoreSlot) frame.post
    at spendCursor
  rcases spendCursor.enterSpendCallerAllowanceThen
      context.invocation.2.2.2 (allowanceError_lookup dp) with
    ⟨body, hget, ⟨coreCursor⟩⟩
  have hbody : body = transferFromCore := by
    simpa [weth10, weth10Aux, transferFromCoreSlot] using hget.symm
  subst body
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferFromSelectLine +++
      (transferFromZero <?> transferFromNonzero)) frame.post at coreCursor
  rcases coreCursor.peelChildlessLine
      (by simp [transferFromSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 1 =? 0] <<+
        targetBranchCursor.pre.stack := by
    unfold transferFromSelectLine at htargetLine
    rcases of_run_append (arg 1) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 1 =? 0) = 0 := by
    simp [B256.eqCheck, hto]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchZero htargetPrefix with
    ⟨nonzeroCursor, _hnonzeroStack⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferFromBalanceCheckLine +++
      ((.call transferBalanceErrorSlot) <?>
        (transferFromNonzeroSuccessLine +++ Func.last .ret)))
    frame.post at nonzeroCursor
  rcases nonzeroCursor.peelChildlessLine
      (by simp [transferFromBalanceCheckLine, loadArgBalanceAmount,
        balanceTooSmall, addressArg, arg, cdl, normalizeAddress,
        pushAddressMask, NinstIsChildless, Ninst.pushB256]) with
    ⟨balanceBranchCursor, -⟩
  rcases balanceBranchCursor.selectBranchSplit with hsuccess | herror
  · rcases hsuccess with ⟨successCursor⟩
    rcases successCursor.peelChildlessLine
        (by simp [transferFromNonzeroSuccessLine, debitLoadedBalance,
          addressArg, arg, cdl, normalizeAddress, pushAddressMask,
          emitTransfer, Blanc.transferFromLog, mstoreAt, logWith,
          pushList, NinstIsChildless, Ninst.pushB256]) with
      ⟨lastCursor, -⟩
    exact lastCursor.finishAttributionInner
  · rcases herror with ⟨errorCursor⟩
    have hrun := Func.Run.of_runCompiled errorCursor.run
    cases hrun with
    | call hget' _hburn hbody' =>
        rw [transferBalanceError_lookup dp] at hget'
        cases Option.some.inj hget'
        exact absurd hbody' Func.not_run_revWith

/-- Nonzero-recipient `transferFrom` transports the allowance region: the
attribution stream is the frame's own record alone, its event is the
wrapper's exact self/max/finite allowance fork, and the core's two
balance-key writes leave every tagged allowance key at the value the
singleton replay prescribes. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferFromNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "transferFrom" [.address, .address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_transferFromNonzero context hselector
      hnonempty hto
  have hneFlash : transferFromSelector ≠ flashLoanSelector := by
    decide +kernel
  have hsel : Sevm.selector frame.sevm = transferFromSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
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
      have hselE : Sevm.selector e = transferFromSelector := hselector
      have hne0 : e.data.length.toB256 ≠ 0 := hnonempty
      have hto' : Sevm.argWord e 1 ≠ 0 := hto
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hcode : Devm.getCode pre ca = Devm.getCode post ca :=
        Exec.installedCodeEq run context.installed
      have hmem : (selector "transferFrom" [.address, .address, .uint256],
          nonpayable transferFrom) ∈ weth10Funcs dp := by
        simp [weth10Funcs]
      rcases exec_enters_weth10Nonpayable_logs run context.invocation.2.2.2
          hselector hne0 hmem with
        ⟨mid, _hvalue, hstor0, _hbal, _hcodeMid, hmemory, _hlogs,
          _houtput, hbody⟩
      have hwfMid : Mem.Wf mid.memory := by
        rw [hmemory]
        exact context.memory_wf
      have hreadsMid : Mem.Reads mid.memory [] := by
        rw [hmemory]
        exact context.memory_reads_empty
      have hlookup :
          ((weth10 dp).main :: weth10Aux)[transferFromCoreSlot]? =
            some transferFromCore := by
        simp [weth10, weth10Aux, transferFromCoreSlot]
      obtain ⟨corePre, hcore, hallowance, _hwfCore, _out, _hreadsCore⟩ :=
        of_spendCallerAllowanceThen_effect dp 2 transferFromCoreSlot
          transferFromCore hlookup hwfMid hreadsMid
          (by simpa only [transferFrom] using hbody)
      have hneApprove : transferFromSelector ≠ approveSelector := by
        decide +kernel
      have hneApproveCall :
          transferFromSelector ≠ approveAndCallSelector := by
        decide +kernel
      have hnePermit : transferFromSelector ≠ permitSelector := by
        decide +kernel
      rcases hallowance.1 with
          ⟨hself, hstorEq, _hlogsEq⟩ |
          ⟨hnself, hmaxOrFinite⟩
      · -- Self-bypass: no event, no allowance write anywhere.
        have hown : (CountedFrame.ofFrame dp ca
            (⟨0, e, pre, .ok post, run, committed⟩ :
              Exec.Frame)).allowance = none := by
          show frameAllowanceEvent e pre post = none
          simp [frameAllowanceEvent, hne0, hselE, hneApprove,
            hneApproveCall, hnePermit, hself]
        refine ⟨fun key hkey => ?_, hcode⟩
        show (Devm.getStor post ca).get key =
          applyAllowanceLedger (Devm.getStor pre ca)
            [CountedFrame.ofFrame dp ca
              ⟨0, e, pre, .ok post, run, committed⟩]
            key
        rw [applyAllowanceLedger_singleton, hown]
        show (Devm.getStor post ca).get key =
          (Devm.getStor pre ca).get key
        rw [← htarget, transferFromCore_allowanceKey dp hkey hto' hcore,
          hstorEq, congrFun hstor0 e.currentTarget]
      · rcases hmaxOrFinite with
            ⟨hmaxGet, hstorEq, _hlogsEq⟩ |
            ⟨allowance, hneMax, _hcover, hallowGet, hstorSet, _hlogsEq⟩
        · -- Infinite allowance: spendMax event, written? is none.
          have hbeforeMax :
              (Devm.getStor pre e.currentTarget).get
                (callerAllowanceRuntimeKey e) = B256.max := by
            rw [← congrFun hstor0 e.currentTarget]
            exact hmaxGet
          have hown : (CountedFrame.ofFrame dp ca
              (⟨0, e, pre, .ok post, run, committed⟩ :
                Exec.Frame)).allowance =
              some { owner := Sevm.argWord e 0
                     spender := e.caller.toB256
                     caller := e.caller
                     depth := e.depth
                     visit := .spendMax } := by
            show frameAllowanceEvent e pre post =
              some { owner := Sevm.argWord e 0
                     spender := e.caller.toB256
                     caller := e.caller
                     depth := e.depth
                     visit := .spendMax }
            simp [frameAllowanceEvent, hne0, hselE, hneApprove,
              hneApproveCall, hnePermit, hnself, hbeforeMax]
          refine ⟨fun key hkey => ?_, hcode⟩
          show (Devm.getStor post ca).get key =
            applyAllowanceLedger (Devm.getStor pre ca)
              [CountedFrame.ofFrame dp ca
                ⟨0, e, pre, .ok post, run, committed⟩]
              key
          rw [applyAllowanceLedger_singleton, hown]
          simp only [AllowanceVisit.written?, ite_self]
          rw [← htarget, transferFromCore_allowanceKey dp hkey hto' hcore,
            hstorEq, congrFun hstor0 e.currentTarget]
        · -- Finite spend: the event's written word is the stored word.
          have hbefore :
              (Devm.getStor pre e.currentTarget).get
                (callerAllowanceRuntimeKey e) = allowance := by
            rw [← congrFun hstor0 e.currentTarget]
            exact hallowGet
          have hown : (CountedFrame.ofFrame dp ca
              (⟨0, e, pre, .ok post, run, committed⟩ :
                Exec.Frame)).allowance =
              some { owner := Sevm.argWord e 0
                     spender := e.caller.toB256
                     caller := e.caller
                     depth := e.depth
                     visit := .spendFinite allowance
                       (allowance - Sevm.argWord e 2) } := by
            show frameAllowanceEvent e pre post =
              some { owner := Sevm.argWord e 0
                     spender := e.caller.toB256
                     caller := e.caller
                     depth := e.depth
                     visit := .spendFinite allowance
                       (allowance - Sevm.argWord e 2) }
            simp [frameAllowanceEvent, hne0, hselE, hneApprove,
              hneApproveCall, hnePermit, hnself, hbefore, hneMax]
          refine ⟨fun key hkey => ?_, hcode⟩
          show (Devm.getStor post ca).get key =
            applyAllowanceLedger (Devm.getStor pre ca)
              [CountedFrame.ofFrame dp ca
                ⟨0, e, pre, .ok post, run, committed⟩]
              key
          rw [applyAllowanceLedger_singleton, hown]
          simp only [AllowanceEvent.key, AllowanceVisit.written?]
          rw [← htarget, transferFromCore_allowanceKey dp hkey hto' hcore,
            hstorSet]
          by_cases hpk :
              projectedAllowanceKey (Sevm.argWord e 0) e.caller.toB256 =
                key
          · rw [if_pos hpk, ← hpk, ← callerAllowanceRuntimeKey_eq_projected]
            exact Stor.get_set_self _ _ _
          · have hne : callerAllowanceRuntimeKey e ≠ key := by
              rw [callerAllowanceRuntimeKey_eq_projected]
              exact hpk
            rw [if_neg hpk, Stor.get_set_ne _ hne _,
              congrFun hstor0 e.currentTarget]

end Weth10

end Blanc
