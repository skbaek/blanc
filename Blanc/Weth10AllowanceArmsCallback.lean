import Blanc.Weth10AllowanceArmsRedeem

/-!
The ERC-677-style callback arms of the allowance-region transport.

`depositToAndCall`, `transferAndCall` and `approveAndCall` all commit a
state prefix inside their own frame and only then spawn the recipient's
`onTokenTransfer`/`onTokenApproval` callback, decoding its Boolean result
in a childless tail.  The frame's own counted record therefore comes
*first*, and the retained callback child's attribution stream follows it,
matching the chronological order in which the writes happened.

The module walks the original retained execution at the counted-cursor
altitude down to the callback `CALL`, crosses that spawn edge while
identifying its counted label with the retained child's attribution
stream, closes the Boolean decoder as a childless suffix, and transports
the allowance region across the child through the `ForallDeeperAt`
recursion hypothesis.  Only `approveAndCall` carries an allowance event;
the other two write balance-region keys alone.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Crossing the retained callback `CALL`

The counted cursor API stops at childless instructions, so this section
adds the one labelled crossing the callback arms need: an exact source
`CALL` whose retained child commits contributes precisely that child's
attribution stream, and nothing else. -/

/-- The counted label of an exact source `CALL` edge is precisely the
retained raw child's attribution stream; the counted mirror of
`Exec.Deriv.ParentStepActions.selected_eq_retained_of_call`. -/
private theorem Exec.Deriv.ParentStepActions.counted_of_call
    {dp : DeployParams} {ca : Adr}
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    {current : Exec pc sevm pre out}
    {continuation : Exec nextPc sevm post out}
    {xl : Xlot} {selected : List FlowAction}
    (hat : Ninst.At sevm.code pc Ninst.call)
    (filled : xl.Filled)
    (step : Ninst.StepRun pc sevm pre Ninst.call xl (.ok post))
    (retained : RetainedXlot xl)
    (commits : retained.RawCommits)
    (edge : Exec.Deriv.ParentStepActions dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩ selected) :
    Exec.Deriv.ParentStepCounted dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩
      (retained.attributionStream dp ca) := by
  cases edge with
  | cont hstep =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨trivial, trivial⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      exact .cont hstep continuation
  | doneOk hstep henter hresume =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      exact .doneOk hstep henter hresume continuation
  | runOk hstep henter child hresume =>
      rename_i spawned resume childEvm raw
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call
            (.some ⟨childEvm, raw⟩) (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_run henter, hresume.symm⟩
      have actualFilled : Xlot.Filled (.some ⟨childEvm, raw⟩) := ⟨child⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled actualFilled step actual).1
      subst xl
      cases retained with
      | some retainedRun =>
          have hrun : retainedRun = child := Subsingleton.elim _ _
          subst retainedRun
          rcases Ninst.step_call_spawn_ofCall hs with ⟨msg, rfl⟩
          have hrawCommits : Execution.commits raw = true := commits
          have hcommit : Blanc.Weth10.Frame.settlementCommits
              (Frame.ofCall msg) raw = true :=
            Frame.settlementCommits_ofCall_of_raw_commits hrawCommits
          have hlabel : RetainedXlot.attributionStream dp ca
              (RetainedXlot.some child) =
              (if h : Blanc.Weth10.Frame.settlementCommits
                    (Frame.ofCall msg) raw = true then
                Exec.frameContribution dp ca
                  (Exec.Frame.ofRun child
                    (Blanc.Weth10.Frame.raw_commits_of_settlementCommits h))
                  (Exec.attributionInner dp ca child)
              else []) := by
            simp [RetainedXlot.attributionStream, Exec.attributionStream,
              hrawCommits, hcommit]
          rw [hlabel]
          exact .runOk hstep henter child hresume continuation

/-- Cross an exact source `CALL` whose retained child commits: the frame's
counted stream splits at precisely that child's attribution stream, and the
continuation carries the compiled tail. -/
private theorem Exec.Frame.CountedCursor.crossCommittedCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {tail : Func} {final rawPost : Devm}
    {rawSlot : Xlot} {rawPc : Nat}
    (cursor : frame.CountedCursor dp ca fs table
      (.next Ninst.call tail) final)
    (rawFilled : rawSlot.Filled)
    (rawStep : Ninst.StepRun rawPc frame.sevm cursor.pre
      Ninst.call rawSlot (.ok rawPost))
    (retained : RetainedXlot rawSlot)
    (commits : retained.RawCommits) :
    ∃ (tailPc : Nat) (next : Exec tailPc frame.sevm rawPost frame.out),
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca ++
          Exec.attributionInner dp ca next ∧
      Func.RunCompiled fs frame.sevm rawPost tail final ∧
      subcode frame.sevm.code.toList tailPc
        (Func.compile table tailPc tail) ∧
      noPushBefore frame.sevm.code tailPc 32 = true := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc Ninst.call :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases cursor.parentPrefix with ⟨before, hbefore⟩
      rcases frame.advance_runCompiled_next cursor.current hbefore hat
          hcompiled with
        ⟨_xl, continuation, _selected, _occurrence, hedge, _hnextPrefix⟩
      rcases hcompiled with ⟨actualSlot, actualFilled, hsteps⟩
      have halign := Ninst.StepRun.unique_exec_of_filled
        rawFilled actualFilled rawStep (hsteps cursor.pc)
      have hslot : rawSlot = actualSlot := halign.1
      subst rawSlot
      have hpost : rawPost = _ := Except.ok.inj halign.2
      subst rawPost
      have hcountedEdge := hedge.counted_of_call hat actualFilled
        (hsteps cursor.pc) retained commits
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      refine ⟨cursor.pc + Ninst.call.size, continuation, ?_, htail,
        nextSub, nextBoundary⟩
      have hp := cursor.countedPrefix.descendantCounted_eq
      have hq := hcountedEdge.descendantCounted_eq
      simp only [Exec.Deriv.descendantCounted, List.nil_append] at hp hq
      rw [hp, hq]

/-! ## Reaching the callback `CALL` at the counted altitude -/

/-- Reach the ERC-677 `CALL` from a counted cursor at the generated
callback body, retaining the exact successful source prefix facts; the
counted mirror of
`Exec.Frame.CompiledCursor.reachCallBoolCallbackWithPrefix`. -/
private theorem Exec.Frame.CountedCursor.reachCallBoolCallbackCounted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {table : List (Nat × Func)}
    {sel targetArg dataArg valueWord : B256} {value : Line}
    {final : Devm} {img : Bytes}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux) table
      (callBoolCallback sel targetArg dataArg value) final)
    (hvalueChildless : ∀ n ∈ value, NinstIsChildless n)
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run frame.sevm a value b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (h_value_mem : Line.Inv Devm.memory value)
    (h_value_logs : Line.Inv Devm.logs value)
    (h_value_output : Line.Inv Devm.output value)
    (h_wf : Mem.Wf cursor.pre.memory)
    (h_reads : Mem.Reads cursor.pre.memory img) :
    ∃ callCursor : frame.CountedCursor dp ca (f₀ :: aux) table
        (.next Ninst.call (.call boolReturnSlot)) final,
      RawTokenCallbackCallPrefix frame.sevm sel targetArg dataArg valueWord
        img cursor.pre callCursor.pre := by
  unfold callBoolCallback at cursor
  rcases cursor.peelChildlessLine
      (line := arg targetArg ++
        [Ninst.dup 0, Ninst.extcodesize, Ninst.iszero])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hcheck⟩
  rcases branchCursor.selectBranchLeftWithBurn (fun _ => not_run_rev) with
    ⟨successCursor, hpopCheck⟩
  rcases successCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨valueCursor, hpop⟩
  rcases valueCursor.peelChildlessLine hvalueChildless with
    ⟨headCursor, hvalueRun⟩
  rcases headCursor.peelChildlessLine
      (line := storeTokenCallbackHead sel)
      (by simp [storeTokenCallbackHead, mstoreAt, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨zerosCursor, hhead⟩
  rcases zerosCursor.peelChildlessLine
      (line := pushList [0, 0])
      (by simp [pushList, NinstIsChildless, Ninst.pushB256]) with
    ⟨tailCursor, hzeros⟩
  rcases tailCursor.peelChildlessLine
      (line := forwardArgTail dataArg 4)
      (by simp [forwardArgTail, arg, cdl, mstoreAt, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨sizeCursor, htailRun⟩
  rcases sizeCursor.peelChildlessLine
      (line := tokenCallbackArgsSize)
      (by simp [tokenCallbackArgsSize, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨offsetCursor, hsize⟩
  rcases offsetCursor.peelChildlessLine
      (line := [Ninst.pushB256 callbackArgsOffset, Ninst.pushB256 0])
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨targetCursor, hoffsets⟩
  rcases targetCursor.peelChildlessLine
      (line := arg targetArg)
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨gasCursor, htargetRun⟩
  rcases gasCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨callCursor, hgas⟩
  exact ⟨callCursor, rawTokenCallbackCallPrefix_of_runs
    sel targetArg dataArg valueWord value h_value_stack h_value_stor
    h_value_bal h_value_code h_value_mem h_value_logs h_value_output
    h_wf h_reads hcheck (Devm.PopBurn.of_popBurnBy hpopCheck) hpop
    hvalueRun hhead hzeros htailRun hsize hoffsets htargetRun hgas⟩

/-! ## The Boolean decoder tail

Packaged over the post-`CALL` continuation as its own retained frame, the
Boolean decoder contributes no counted records: its bubble and short
returndata arms cannot reach a committed final state, and its decode arm
is a childless line ending in `RETURN`. -/

private theorem Exec.attributionInner_eq_nil_of_boolReturnTail
    {dp : DeployParams} {ca : Adr}
    {fsevm : Sevm} {pcT : Nat} {midD final : Devm} {out : Execution}
    (next : Exec pcT fsevm midD out)
    (committed : Execution.commits out = true)
    (htail : Func.RunCompiled ((weth10 dp).main :: weth10Aux) fsevm midD
      (.call boolReturnSlot) final)
    (hsub : subcode fsevm.code.toList pcT
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) pcT
        (.call boolReturnSlot)))
    (hbound : noPushBefore fsevm.code pcT 32 = true)
    (hcode : some fsevm.code.toList = Prog.compile (weth10 dp)) :
    Exec.attributionInner dp ca next = [] := by
  let tailFrame : Exec.Frame := ⟨pcT, fsevm, midD, out, next, committed⟩
  let tailCursor : Exec.Frame.CountedCursor dp ca tailFrame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (.call boolReturnSlot) final :=
    ⟨pcT, midD, next, ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, htail, hsub, hbound⟩
  rcases tailCursor.enterCall hcode with ⟨body, hget, ⟨bodyCursor⟩⟩
  have hbody : body = boolReturn := by
    simpa [weth10, weth10Aux, boolReturnSlot] using hget.symm
  subst body
  unfold boolReturn at bodyCursor
  rcases bodyCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨firstBranchCursor, -⟩
  rcases firstBranchCursor.selectBranchSplit with hdecode | hbubble
  · rcases hdecode with ⟨decodePrefixCursor⟩
    rcases decodePrefixCursor.peelChildlessLine
        (line := retdataShorterThan 32)
        (by simp [retdataShorterThan, NinstIsChildless,
          Ninst.pushB256]) with
      ⟨secondBranchCursor, -⟩
    rcases secondBranchCursor.selectBranchSplit with hreturn | hrev
    · rcases hreturn with ⟨returnCursor⟩
      change Exec.Frame.CountedCursor dp ca tailFrame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        ((pushList [32, 0, 0] ++
          [Ninst.retdatacopy, Ninst.pushB256 0, Ninst.mload,
            Ninst.iszero, Ninst.iszero] ++
          mstoreAt 0 ++ pushList [32, 0]) +++ Func.ret) final
        at returnCursor
      rcases returnCursor.peelChildlessLine
          (by simp [pushList, mstoreAt, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨lastCursor, -⟩
      exact lastCursor.finishAttributionInner
    · rcases hrev with ⟨revCursor⟩
      exact absurd (Func.Run.of_runCompiled revCursor.run) not_run_rev
  · rcases hbubble with ⟨bubbleCursor⟩
    rcases bubbleCursor.enterCall hcode with
      ⟨bubbleBody, hbubbleGet, ⟨bubbleBodyCursor⟩⟩
    have hb : bubbleBody = bubbleRevert := by
      simpa [weth10, weth10Aux, bubbleRevertSlot] using hbubbleGet.symm
    subst bubbleBody
    exact (not_run_bubbleRevert
      (Func.Run.of_runCompiled bubbleBodyCursor.run)).elim

/-! ## The counted callback chronology -/

/-- Exact counted chronology for one generated ERC-677 callback: the raw
callback boundary and the retained child whose attribution stream is
precisely the frame's whole proper-descendant counted stream.  The counted
mirror of `Exec.Frame.CompiledCursor.compiledTokenCallbackChronology`. -/
private theorem Exec.Frame.CountedCursor.countedTokenCallbackChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {sel targetArg dataArg valueWord : B256} {value : Line} {img : Bytes}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (callBoolCallback sel targetArg dataArg value) frame.post)
    (hvalueChildless : ∀ n ∈ value, NinstIsChildless n)
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run frame.sevm a value b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (h_value_mem : Line.Inv Devm.memory value)
    (h_value_logs : Line.Inv Devm.logs value)
    (h_value_output : Line.Inv Devm.output value)
    (h_wf : Mem.Wf cursor.pre.memory)
    (h_reads : Mem.Reads cursor.pre.memory img)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    ∃ (inputSize : B256) (input : Bytes)
        (callPre callPost parent child : Devm) (xl : Xlot) (pc : Nat)
        (retained : RetainedXlot xl),
      RawTokenCallbackIndexedStepBoundary dp frame.sevm
        frame.sevm.currentTarget (Sevm.argWord frame.sevm targetArg).toAdr
        (Sevm.argWord frame.sevm targetArg) sel valueWord
        (Sevm.tailLen frame.sevm dataArg) inputSize
        (Sevm.tailBytes frame.sevm dataArg) input cursor.pre frame.post
        callPre callPost parent child xl pc ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  rcases cursor.reachCallBoolCallbackCounted hvalueChildless h_value_stack
      h_value_stor h_value_bal h_value_code h_value_mem h_value_logs
      h_value_output h_wf h_reads with
    ⟨callCursor, hprefix⟩
  have compiled := callCursor.run
  cases compiled with
  | next hcallCompiled hboolCompiled =>
      have hcall := Ninst.Run.of_runCompiled hcallCompiled
      have hbool := Func.Run.of_runCompiled hboolCompiled
      rcases rawTokenCallbackIndexedStepBoundary_of_prefix dp sel
          targetArg dataArg valueWord hprefix hcall hbool with
        ⟨inputSize, input, parent, child, xl, pc, hraw⟩
      have hrawData := hraw
      rcases hrawData with
        ⟨_htargetEq, _hsize, _delegated, _code, _gasWord, _avail, hstep,
          _hdepth, _hstack, _hinput, _himage, _hstor, _hbal, _hcodePre,
          _hlogs, _houtput, _hparentState, _hparentMemory, _hparentLogs,
          _hparentOutput, _hdelegation, hfilled, hmessage, hclean,
          _hresume, _hcallPostState, _hreturnData, _hmemory,
          _hcallPostStack, _hcontinuation⟩
      obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
      have hcommits : retained.RawCommits := by
        cases retained with
        | none => trivial
        | some retainedRun =>
            exact Frame.raw_commits_of_settlementCommits
              (ProcessMessage.settlementCommits_of_some_ok_clean
                hmessage hclean)
      rcases callCursor.crossCommittedCall hfilled hstep retained
          hcommits with
        ⟨tailPc, tailExec, hsplit, htailRun, htailSub, htailBound⟩
      have htailNil : Exec.attributionInner dp ca tailExec = [] :=
        Exec.attributionInner_eq_nil_of_boolReturnTail tailExec
          frame.committed htailRun htailSub htailBound hcode
      exact ⟨inputSize, input, callCursor.pre, _, parent, child, xl, pc,
        retained, hraw, by rw [hsplit, htailNil, List.append_nil]⟩

/-! ## Allowance transport across the retained callback -/

/-- Exact allowance-region effect of a retained ERC-677 callback boundary;
the allowance mirror of
`RawTokenCallbackIndexedStepBoundary.storageSegmentEffect`.  The supplied
retained witness is the one selected by the enclosing counted execution, so
the resulting ledger is definitionally that exact slot's stream. -/
private theorem RawTokenCallbackIndexedStepBoundary.allowanceRegionEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {self target : Adr}
    {rawTarget sel value tailLen inputSize : B256} {tail input : Bytes}
    {pre post callPre callPost parent child : Devm} {xl : Xlot}
    {pc : Nat}
    (callback : RawTokenCallbackIndexedStepBoundary dp e self target
      rawTarget sel value tailLen inputSize tail input pre post callPre
      callPost parent child xl pc)
    (retained : RetainedXlot xl)
    (hself : e.currentTarget = ca)
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm childPre out)) :
    AllowanceRegionEffect ca pre post
      (retained.attributionStream dp ca) := by
  rcases callback with
    ⟨_targetEq, _inputSizeEq, delegated, code, gasWord, avail, _hstep,
      hdepth, _hstack, _hinput, _himage, hstorPre, _hbalPre, hcodePre,
      _hlogsPre, _houtputPre, hparentState, _hparentMemory, _hparentLogs,
      _hparentOutput, hdelegation, _hfilled, hprocess, _hclean, _hresume,
      hcallPostState, _hreturnData, _hcallPostMemory, _hcallPostStack,
      hcontinuation⟩
  let msg := callMsg e parent (min gasWord.toNat (except64th avail)) 0
    self target target true false input code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hcallPreCode : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hcodePre ca]
    exact installed
  have hparent : callPre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    dsimp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    exact callbackCode_eq_compiled_of_target_eq hcallPreCode htargetCa
      hdelegation
  have htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    simp [msg, callMsg, htargetCa]
  have childEffect := trace.allowanceRegionDelta_of_forallDeeperAt hparent
    hmsgDepth hcallPreCode htargetCode htargetDirect hdeeper
  have hprefix := AllowanceRegionEffect.of_getStorCode_eq
    (congrFun hstorPre ca) (congrFun hcodePre ca)
  have hchildToCallPost := AllowanceRegionEffect.of_getStorCode_eq
    (congrArg (fun state : State => state.getStor ca) hcallPostState.symm)
    (congrArg (fun state : State => state.getCode ca) hcallPostState.symm)
  obtain ⟨htailStor, _, htailCode⟩ :=
    of_run_call_boolReturn_preserves_fields dp hcontinuation
  have hsuffix := AllowanceRegionEffect.of_getStorCode_eq
    (congrFun htailStor ca) (by simpa only [hself] using htailCode)
  have combined := hprefix.append
    (childEffect.append (hchildToCallPost.append hsuffix))
  simpa only [List.nil_append, List.append_nil, trace] using combined

/-! ## The `depositToAndCall` arm -/

/-- `depositToAndCall` transports the allowance region.  Its committed
prefix mints at one normalized address-shaped balance key and its own
record carries no allowance event, so that record replays transparently
ahead of the retained callback child's attribution stream. -/
theorem Exec.Frame.allowanceRegionEffect_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, depositToAndCall) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [depositToAndCallSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨bodyCursor, hentrySilent⟩
  unfold depositToAndCall at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := mintToPrefix)
      (by simp [mintToPrefix, addressArg, arg, cdl, normalizeAddress,
        pushAddressMask, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨callbackCursor, hmint⟩
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hentrySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hentrySilent.memory]
    exact context.memory_reads_empty
  rcases mintToPrefix_effect hwfBody hreadsBody hmint with
    ⟨hstor, _hlogs, _hbal, hcodeMint, _houtput⟩
  rcases mintToPrefix_callbackMemoryFrame hwfBody hreadsBody hmint with
    ⟨hwfCallback, hreadsCallback⟩
  rcases callbackCursor.countedTokenCallbackChronology
      (sel := onTokenTransferSelector) (targetArg := 0) (dataArg := 1)
      (valueWord := frame.sevm.value) (value := [Ninst.callvalue])
      (img := frame.sevm.value.toBytes)
      (by simp [NinstIsChildless])
      (by
        intro a b xs hp hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_callvalue hcv) hp)
      (by line_inv) (by line_inv) (by line_inv) (by line_inv)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).logs)
      (by
        intro e' a b hline
        rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
        cases hnil
        exact (of_run_callvalue hcv).output)
      hwfCallback hreadsCallback context.invocation.2.2.2 with
    ⟨_inputSize, _input, _callPre, _callPost, _parent, _child, _xl, _pc,
      retained, callback, hinner⟩
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorEntry : Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
    funext (getStor_eq_of_state_eq hentrySilent.state)
  have hcodeEntry : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hentrySilent.state)
  have hcodeCallback : Devm.getCode frame.pre ca =
      Devm.getCode callbackCursor.pre ca :=
    (congrFun hcodeEntry ca).trans (congrFun hcodeMint ca).symm
  have installedCallback : some (callbackCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCallback]
    exact context.installed.1
  have childEffect := callback.allowanceRegionEffect retained htarget
    installedCallback hdeeper
  have hneFlash : depositToAndCallSelector ≠ flashLoanSelector := by
    decide +kernel
  have hsel : Sevm.selector frame.sevm = depositToAndCallSelector :=
    hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        retained.attributionStream dp ca := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq, hinner,
      Exec.frameContribution_eq_cons dp ca frame _
        context.invocation hnotflash]
  rw [hstream]
  have hneApprove : depositToAndCallSelector ≠ approveSelector := by
    decide +kernel
  have hneApproveCall :
      depositToAndCallSelector ≠ approveAndCallSelector := by
    decide +kernel
  have hnePermit : depositToAndCallSelector ≠ permitSelector := by
    decide +kernel
  have hneTransferFrom :
      depositToAndCallSelector ≠ transferFromSelector := by
    decide +kernel
  have hneWithdrawFrom :
      depositToAndCallSelector ≠ withdrawFromSelector := by
    decide +kernel
  have hneAllowance : depositToAndCallSelector ≠ allowanceSelector := by
    decide +kernel
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hsel, hneApprove, hneApproveCall,
      hnePermit, hneTransferFrom, hneWithdrawFrom, hneFlash, hneAllowance]
  have hvalid : ValidAdr (normalizedAddressArg frame.sevm 0) :=
    normalizedAddress_valid (Sevm.argWord frame.sevm 0)
  have hstorCa := hstor
  rw [htarget] at hstorCa
  have hprefixEffect : AllowanceRegionEffect ca frame.pre
      callbackCursor.pre [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨fun key hkey => ?_, hcodeCallback⟩
    rw [applyAllowanceLedger_singleton, hown]
    show (Devm.getStor callbackCursor.pre ca).get key =
      (Devm.getStor frame.pre ca).get key
    rw [hstorCa,
      Stor.get_set_ne _ ((allowanceRegion_ne_validAdr hkey hvalid).symm) _,
      ← congrFun hstorEntry ca]
  exact hprefixEffect.append childEffect

/-! ## The `transferAndCall` arm -/

/-- The nonzero-recipient `transferAndCall` prefix writes exactly two
address-shaped balance keys — the caller's debit and the normalized
recipient's credit — so every tagged allowance key keeps its entry value,
and its `Transfer` emission leaves the callback's memory frame holding the
raw amount word. -/
private theorem transferAndCallPrefix_frame
    {e : Sevm} {s0 s1 s2 s3 s4 : Devm} {balance : B256}
    (hp : balance :: Sevm.argWord e 1 :: e.caller.toB256 :: [] <<+ s0.stack)
    (hwf : Mem.Wf s0.memory)
    (hreads : Mem.Reads s0.memory [])
    (hdebit : Line.Run e s0 debitLoadedBalance s1)
    (hcredit : Line.Run e s1 (addressArg 0 ++ [Ninst.dup 0, Ninst.sload] ++
      arg 1 ++ [Ninst.add, Ninst.swap 0, Ninst.sstore]) s2)
    (hevent : Line.Run e s2 ([Ninst.caller] ++ arg 1 ++ addressArg 0) s3)
    (hemit : Line.Run e s3 emitTransfer s4) :
    (∀ key, InRegion .allowance key →
      (Devm.getStor s4 e.currentTarget).get key =
        (Devm.getStor s0 e.currentTarget).get key) ∧
    Devm.getCode s4 = Devm.getCode s0 ∧
    Mem.Wf s4.memory ∧
    Mem.Reads s4.memory (Sevm.argWord e 1).toBytes := by
  unfold debitLoadedBalance at hdebit
  rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
  have hpD1 : (balance - Sevm.argWord e 1) :: e.caller.toB256 :: [] <<+
      d1.stack := prefix_of_sub hsub hp
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
  have hsetDebit : Devm.getStor s1 e.currentTarget =
      (Devm.getStor d2 e.currentTarget).set e.caller.toB256
        (balance - Sevm.argWord e 1) :=
    sstore_getStor_set hstore hpD2
  rcases of_run_append (addressArg 0) hcredit with ⟨c1, haddr, hcredit1⟩
  have hpC1 : ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c1.stack :=
    prefix_of_addressArg nil_pref haddr
  rcases of_run_append [Ninst.dup 0] hcredit1 with ⟨c2, hdupLine, hcredit2⟩
  rcases Line.of_run_cons hdupLine with ⟨c2', hdup, hnil2⟩
  cases hnil2
  have hpC2 : ((~~~ addressMask) &&& Sevm.argWord e 0) ::
      ((~~~ addressMask) &&& Sevm.argWord e 0) :: [] <<+ c2.stack :=
    prefix_of_dup_val hdup (by show_nth) hpC1
  rcases of_run_append [Ninst.sload] hcredit2 with ⟨c3, hloadLine, hcredit3⟩
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
  have hsetCredit : Devm.getStor s2 e.currentTarget =
      (Devm.getStor c6 e.currentTarget).set
        ((~~~ addressMask) &&& Sevm.argWord e 0)
        (Sevm.argWord e 1 + toBal) :=
    sstore_getStor_set hstoreN hpC6
  have heventRun := hevent
  rcases Line.of_run_cons hevent with ⟨afterCaller, hcaller, hevent1⟩
  have hpCaller : e.caller.toB256 :: [] <<+ afterCaller.stack :=
    prefix_of_push (of_run_caller hcaller) nil_pref
  rcases of_run_append (arg 1) hevent1 with ⟨afterAmount, hamountE, haddress⟩
  have hpAmount : Sevm.argWord e 1 :: e.caller.toB256 :: [] <<+
      afterAmount.stack := prefix_of_arg hpCaller hamountE
  have hpEvent : normalizedAddressArg e 0 :: Sevm.argWord e 1 ::
      e.caller.toB256 :: [] <<+ s3.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg hpAmount haddress
  have hmem03 : s0.memory = s3.memory := by
    calc
      s0.memory = d1.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)
      _ = d2.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hswap Line.Run.nil)
      _ = s1.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hstore Line.Run.nil)
      _ = s2.memory := Line.of_inv Devm.memory (by line_inv) hcredit
      _ = s3.memory := Line.of_inv Devm.memory (by line_inv) heventRun
  have hwfEvent : Mem.Wf s3.memory := by
    rw [← hmem03]
    exact hwf
  have hreadsEvent : Mem.Reads s3.memory [] := by
    rw [← hmem03]
    exact hreads
  obtain ⟨_hpNext, _hemitLogs, hemitStor, _hemitBal, hemitCode,
      _hemitOutput, hwf4, hreads4⟩ :=
    emitTransfer_effect_frame hpEvent hwfEvent hreadsEvent hemit
  have hwrite : Bytes.writeAt [] 0 (Sevm.argWord e 1).toBytes =
      (Sevm.argWord e 1).toBytes :=
    Bytes.writeAt_zero_of_le (Nat.zero_le _)
  rw [hwrite] at hreads4
  have hsInv1 : Devm.getStor s0 = Devm.getStor d2 :=
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hsub Line.Run.nil)).trans
      (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil))
  have hsInv2 : Devm.getStor s1 = Devm.getStor c6 := by
    rw [Line.of_inv Devm.getStor (by line_inv) haddr,
      Line.of_inv Devm.getStor (by line_inv) hdupLine,
      Line.of_inv Devm.getStor (by line_inv) hloadLine,
      Line.of_inv Devm.getStor (by line_inv) hamount,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons haddN Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswapN Line.Run.nil)]
  have hsInv3 : Devm.getStor s2 = Devm.getStor s3 :=
    Line.of_inv Devm.getStor (by line_inv) heventRun
  refine ⟨fun key hkey => ?_, ?_, hwf4, hreads4⟩
  · have hneCaller : e.caller.toB256 ≠ key :=
      (allowanceRegion_ne_validAdr hkey ⟨e.caller, rfl⟩).symm
    have hneNorm : ((~~~ addressMask) &&& Sevm.argWord e 0) ≠ key :=
      (allowanceRegion_ne_validAdr hkey
        (normalizedAddress_valid (Sevm.argWord e 0))).symm
    rw [congrFun hemitStor e.currentTarget,
      ← congrFun hsInv3 e.currentTarget, hsetCredit,
      Stor.get_set_ne _ hneNorm _, ← congrFun hsInv2 e.currentTarget,
      hsetDebit, Stor.get_set_ne _ hneCaller _,
      ← congrFun hsInv1 e.currentTarget]
  · calc
      Devm.getCode s4 = Devm.getCode s3 := hemitCode
      _ = Devm.getCode s2 :=
        (Line.of_inv Devm.getCode (by line_inv) heventRun).symm
      _ = Devm.getCode s1 :=
        (Line.of_inv Devm.getCode (by line_inv) hcredit).symm
      _ = Devm.getCode s0 :=
        (Line.of_inv Devm.getCode (by line_inv) hdebit).symm

/-- Nonzero-recipient `transferAndCall` transports the allowance region: the
frame's own record carries no allowance event and replays transparently,
and the retained callback child supplies the rest of the ledger. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transferAndCall) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferAndCallSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  unfold transferAndCall transferThen at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := arg 0 ++ [Ninst.iszero])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 0 =? 0] <<+ targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 0 =? 0) = 0 := by
    simp [B256.eqCheck, hto]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchZeroSilent htargetPrefix with
    ⟨nonzeroCursor, _hnonzeroStack, hselectSilent⟩
  rcases nonzeroCursor.peelChildlessLine
      (line := loadCallerBalanceAmount 1 ++ balanceTooSmall)
      (by simp [loadCallerBalanceAmount, balanceTooSmall, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨guardBranchCursor, hguardLine⟩
  rcases guardBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith (transferBalanceError_lookup dp)) with
    ⟨successCursor, hsuccessPop⟩
  rcases of_run_append (loadCallerBalanceAmount 1) hguardLine with
    ⟨afterLoad, hload, hsmall⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, _hbalance, hpLoad⟩
  have hpFlag := prefix_of_balanceTooSmall hpLoad hsmall
  have hsuccessStack := popBurn_pref
    (Devm.PopBurn.of_popBurnBy hsuccessPop) hpFlag
  rcases successCursor.peelChildlessLine
      (line := debitLoadedBalance)
      (by simp [debitLoadedBalance, NinstIsChildless]) with
    ⟨creditCursor, hdebit⟩
  rcases creditCursor.peelChildlessLine
      (line := addressArg 0 ++ [Ninst.dup 0, Ninst.sload] ++ arg 1 ++
        [Ninst.add, Ninst.swap 0, Ninst.sstore])
      (by simp [addressArg, normalizeAddress, pushAddressMask, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, hcredit⟩
  rcases eventCursor.peelChildlessLine
      (line := [Ninst.caller] ++ arg 1 ++ addressArg 0)
      (by simp [addressArg, normalizeAddress, pushAddressMask, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨emitCursor, hevent⟩
  rcases emitCursor.peelChildlessLine
      (line := emitTransfer)
      (by simp [emitTransfer, Blanc.transferFromLog, mstoreAt, logWith,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨callbackCursor, hemit⟩
  have hmemSuccess : frame.pre.memory = successCursor.pre.memory := by
    calc
      frame.pre.memory = bodyCursor.pre.memory := hbodySilent.memory
      _ = targetBranchCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) htargetLine
      _ = nonzeroCursor.pre.memory := hselectSilent.memory
      _ = guardBranchCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hguardLine
      _ = successCursor.pre.memory := hsuccessPop.memory
  have hwfSuccess : Mem.Wf successCursor.pre.memory := by
    rw [← hmemSuccess]
    exact context.memory_wf
  have hreadsSuccess : Mem.Reads successCursor.pre.memory [] := by
    rw [← hmemSuccess]
    exact context.memory_reads_empty
  obtain ⟨hprefixKey, hprefixCode, hwfCallback, hreadsCallback⟩ :=
    transferAndCallPrefix_frame hsuccessStack.2 hwfSuccess hreadsSuccess
      hdebit hcredit hevent hemit
  rcases callbackCursor.countedTokenCallbackChronology
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
      hwfCallback hreadsCallback context.invocation.2.2.2 with
    ⟨_inputSize, _input, _callPre, _callPost, _parent, _child, _xl, _pc,
      retained, callback, hinner⟩
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorSuccess : Devm.getStor frame.pre = Devm.getStor
      successCursor.pre := by
    calc
      Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
        funext (getStor_eq_of_state_eq hbodySilent.state)
      _ = Devm.getStor targetBranchCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv) htargetLine
      _ = Devm.getStor nonzeroCursor.pre :=
        funext (getStor_eq_of_state_eq hselectSilent.state)
      _ = Devm.getStor guardBranchCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv) hguardLine
      _ = Devm.getStor successCursor.pre :=
        funext (getStor_eq_of_state_eq hsuccessPop.state)
  have hcodeSuccess : Devm.getCode frame.pre = Devm.getCode
      successCursor.pre := by
    calc
      Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
        funext (getCode_eq_of_state_eq hbodySilent.state)
      _ = Devm.getCode targetBranchCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) htargetLine
      _ = Devm.getCode nonzeroCursor.pre :=
        funext (getCode_eq_of_state_eq hselectSilent.state)
      _ = Devm.getCode guardBranchCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hguardLine
      _ = Devm.getCode successCursor.pre :=
        funext (getCode_eq_of_state_eq hsuccessPop.state)
  have hcodeCallback : Devm.getCode frame.pre ca =
      Devm.getCode callbackCursor.pre ca :=
    (congrFun hcodeSuccess ca).trans (congrFun hprefixCode ca).symm
  have installedCallback : some (callbackCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCallback]
    exact context.installed.1
  have childEffect := callback.allowanceRegionEffect retained htarget
    installedCallback hdeeper
  have hneFlash : transferAndCallSelector ≠ flashLoanSelector := by
    decide +kernel
  have hsel : Sevm.selector frame.sevm = transferAndCallSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        retained.attributionStream dp ca := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq, hinner,
      Exec.frameContribution_eq_cons dp ca frame _
        context.invocation hnotflash]
  rw [hstream]
  have hneApprove : transferAndCallSelector ≠ approveSelector := by
    decide +kernel
  have hneApproveCall :
      transferAndCallSelector ≠ approveAndCallSelector := by
    decide +kernel
  have hnePermit : transferAndCallSelector ≠ permitSelector := by
    decide +kernel
  have hneTransferFrom :
      transferAndCallSelector ≠ transferFromSelector := by
    decide +kernel
  have hneWithdrawFrom :
      transferAndCallSelector ≠ withdrawFromSelector := by
    decide +kernel
  have hneAllowance : transferAndCallSelector ≠ allowanceSelector := by
    decide +kernel
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hsel, hneApprove, hneApproveCall,
      hnePermit, hneTransferFrom, hneWithdrawFrom, hneFlash, hneAllowance]
  have hprefixKeyCa := hprefixKey
  rw [htarget] at hprefixKeyCa
  have hprefixEffect : AllowanceRegionEffect ca frame.pre
      callbackCursor.pre [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨fun key hkey => ?_, hcodeCallback⟩
    rw [applyAllowanceLedger_singleton, hown]
    show (Devm.getStor callbackCursor.pre ca).get key =
      (Devm.getStor frame.pre ca).get key
    rw [hprefixKeyCa key hkey, ← congrFun hstorSuccess ca]
  exact hprefixEffect.append childEffect

/-! ## The zero-recipient `transferAndCall` arm

`transferAndCall` is `transferThen` applied to the ERC-677 callback, so a
zero recipient word routes it into `transferZeroThen`: the frame burns the
caller's balance and redeems it with an external value `CALL`, and only then
runs the callback.  This leaf therefore composes the redemption walk of
`Weth10AllowanceArmsRedeem` with the callback chronology above, the
redemption walk's generic success continuation being exactly the callback.
Both retained children are transported by the recursion hypothesis, and the
frame's own record — a `transferAndCall` selector — carries no allowance
event. -/

/-- The ERC-677 callback closes a redemption walk: whatever counted stream
the callback continuation retains is precisely its own child's attribution
stream, transported across the tagged allowance region by the recursion
hypothesis. -/
private theorem Exec.Frame.tokenCallbackSuccessAllowanceCloser
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {dataArg : B256}
    (htarget : frame.sevm.currentTarget = ca)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    SuccessAllowanceCloser dp ca frame
      (Sevm.argWord frame.sevm 1).toBytes
      (callBoolCallback onTokenTransferSelector 0 dataArg (arg 1)) := by
  intro entryPc entry continuation hrun hsub hbound hwfEntry hreadsEntry
    hcodeEntry key hkey
  let suffixCursor :
      (⟨entryPc, frame.sevm, entry, frame.out, continuation,
          frame.committed⟩ : Exec.Frame).CountedCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (callBoolCallback onTokenTransferSelector 0 dataArg (arg 1))
        frame.post :=
    ⟨entryPc, entry, continuation,
      ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, hrun, hsub, hbound⟩
  rcases suffixCursor.countedTokenCallbackChronology
      (sel := onTokenTransferSelector) (targetArg := 0) (dataArg := dataArg)
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
      hwfEntry hreadsEntry hcode with
    ⟨_inputSize, _input, _callPre, _callPost, _parent, _child, _xl, _pc,
      retained, callback, hinner⟩
  have childEffect := callback.allowanceRegionEffect retained htarget
    hcodeEntry hdeeper
  rw [show Exec.attributionInner dp ca continuation =
      retained.attributionStream dp ca from hinner]
  exact childEffect.storage key hkey

/-- Zero-recipient `transferAndCall` transports the allowance region.  The
zero word selects `transferThen`'s redemption branch, so the frame debits the
caller's balance key, sends the redeemed ether, and only then spawns the
ERC-677 callback; neither retained child is the frame's own record, which
carries no allowance event and replays transparently ahead of them. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferAndCallZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hzero : Sevm.argWord frame.sevm 0 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transferAndCall) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferAndCallSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨transferCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre transferCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  unfold transferAndCall transferThen at transferCursor
  rcases transferCursor.peelChildlessLine
      (line := arg 0 ++ [Ninst.iszero])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 0 =? 0] <<+ targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzeroRun, hnil⟩
    cases hnil
    exact prefix_of_iszero hzeroRun (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 0 =? 0) = 1 := by
    simp [B256.eqCheck, hzero]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨bodyCursor, _hbodyStack, hbranchSilent⟩
  have hlineStor : Devm.getStor transferCursor.pre =
      Devm.getStor targetBranchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) htargetLine
  have hlineCode : Devm.getCode transferCursor.pre =
      Devm.getCode targetBranchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) htargetLine
  have hlineMem : transferCursor.pre.memory = targetBranchCursor.pre.memory :=
    Line.of_inv Devm.memory (by line_inv) htargetLine
  have hbodyStor : Devm.getStor frame.pre ca =
      Devm.getStor bodyCursor.pre ca :=
    (getStor_eq_of_state_eq hbodySilent.state ca).trans
      ((congrFun hlineStor ca).trans
        (getStor_eq_of_state_eq hbranchSilent.state ca))
  have hbodyCode : Devm.getCode frame.pre ca =
      Devm.getCode bodyCursor.pre ca :=
    (getCode_eq_of_state_eq hbodySilent.state ca).trans
      ((congrFun hlineCode ca).trans
        (getCode_eq_of_state_eq hbranchSilent.state ca))
  have hbodyMem : frame.pre.memory = bodyCursor.pre.memory :=
    hbodySilent.memory.trans (hlineMem.trans hbranchSilent.memory)
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemBody 1 redeemSendToCallerPrefix
      (callBoolCallback onTokenTransferSelector 0 2 (arg 1)))
    frame.post at bodyCursor
  have hstorage := bodyCursor.redeemAllowanceRegionStorage
    (target := frame.sevm.caller.toB256)
    context.invocation.2.1 nil_pref
    (by rw [← hbodyMem]; exact context.memory_wf)
    (by rw [← hbodyMem]; exact context.memory_reads_empty)
    (by
      rw [← hbodyCode]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by
      rw [Bytes.writeAt_zero_of_le (Nat.zero_le _)]
      exact frame.tokenCallbackSuccessAllowanceCloser context.invocation.2.1
        context.invocation.2.2.2 hdeeper)
    hdeeper
  have hneFlash : transferAndCallSelector ≠ flashLoanSelector := by
    decide +kernel
  have hneApprove : transferAndCallSelector ≠ approveSelector := by
    decide +kernel
  have hneApproveCall :
      transferAndCallSelector ≠ approveAndCallSelector := by
    decide +kernel
  have hnePermit : transferAndCallSelector ≠ permitSelector := by
    decide +kernel
  have hneTransferFrom :
      transferAndCallSelector ≠ transferFromSelector := by
    decide +kernel
  have hneWithdrawFrom :
      transferAndCallSelector ≠ withdrawFromSelector := by
    decide +kernel
  have hneAllowance : transferAndCallSelector ≠ allowanceSelector := by
    decide +kernel
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hselector, hneFlash]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
      hneApproveCall, hnePermit, hneTransferFrom, hneWithdrawFrom,
      hneFlash, hneAllowance]
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotflash]
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  rw [applyAllowanceLedger_cons_none hown]
  rw [hstorage key hkey]
  exact applyAllowanceLedger_congr
    (congrArg (fun s : Stor => s.get key) hbodyStor.symm)

/-! ## The `approveAndCall` arm -/

/-- `approveAndCall` transports the allowance region.  Unlike the other two
callback arms its own record does carry an allowance event — the same
`.approveStore` branch `approve` takes — and the committed prefix stores
exactly at that event's projected key before the callback child is
spawned, so the record replays ahead of the child's stream. -/
theorem Exec.Frame.allowanceRegionEffect_of_approveAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = approveAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable approveAndCall) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [approveAndCallSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  unfold approveAndCall at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := approvePrefix)
      (by simp [approvePrefix, allowanceKeyFromMemory, Blanc.logApprove,
        argCopy, cdc, arg, cdl, mstoreAt, logWith, pushList,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨callbackCursor, hprefix⟩
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hbodySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hbodySilent.memory]
    exact context.memory_reads_empty
  rcases approvePrefix_callbackFrame nil_pref hwfBody hreadsBody
      hprefix with
    ⟨hstor, _hlogs, _hbal, hcodeApprove, _houtput, hwfCallback,
      callbackImg, hreadsCallback⟩
  rcases callbackCursor.countedTokenCallbackChronology
      (sel := onTokenApprovalSelector) (targetArg := 0) (dataArg := 2)
      (valueWord := Sevm.argWord frame.sevm 1) (value := arg 1)
      (img := callbackImg)
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
      hwfCallback hreadsCallback context.invocation.2.2.2 with
    ⟨_inputSize, _input, _callPre, _callPost, _parent, _child, _xl, _pc,
      retained, callback, hinner⟩
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  have hstorEntry : Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
    funext (getStor_eq_of_state_eq hbodySilent.state)
  have hcodeEntry : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hbodySilent.state)
  have hcodeCallback : Devm.getCode frame.pre ca =
      Devm.getCode callbackCursor.pre ca :=
    (congrFun hcodeEntry ca).trans (congrFun hcodeApprove ca).symm
  have installedCallback : some (callbackCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCallback]
    exact context.installed.1
  have childEffect := callback.allowanceRegionEffect retained htarget
    installedCallback hdeeper
  have hneFlash : approveAndCallSelector ≠ flashLoanSelector := by
    decide +kernel
  have hsel : Sevm.selector frame.sevm = approveAndCallSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        retained.attributionStream dp ca := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq, hinner,
      Exec.frameContribution_eq_cons dp ca frame _
        context.invocation hnotflash]
  rw [hstream]
  have hown : (CountedFrame.ofFrame dp ca frame).allowance =
      some { owner := frame.sevm.caller.toB256
             spender := Sevm.argWord frame.sevm 0
             caller := frame.sevm.caller
             depth := frame.sevm.depth
             visit := .approveStore (Sevm.argWord frame.sevm 1) } := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post =
      some { owner := frame.sevm.caller.toB256
             spender := Sevm.argWord frame.sevm 0
             caller := frame.sevm.caller
             depth := frame.sevm.depth
             visit := .approveStore (Sevm.argWord frame.sevm 1) }
    simp [frameAllowanceEvent, hnonempty, hsel]
  have hstorCa := hstor
  rw [htarget] at hstorCa
  have hprefixEffect : AllowanceRegionEffect ca frame.pre
      callbackCursor.pre [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨fun key hkey => ?_, hcodeCallback⟩
    rw [congrFun hstorEntry ca, applyAllowanceLedger_singleton, hown]
    simp only [AllowanceEvent.key, AllowanceVisit.written?]
    show (Devm.getStor callbackCursor.pre ca).get key = _
    rw [hstorCa]
    by_cases hkeyEq : projectedAllowanceKey frame.sevm.caller.toB256
        (Sevm.argWord frame.sevm 0) = key
    · rw [if_pos hkeyEq, ← hkeyEq, ← approveRuntimeKey_eq_projected]
      exact Stor.get_set_self _ _ _
    · rw [if_neg hkeyEq]
      apply Stor.get_set_ne
      rw [approveRuntimeKey_eq_projected]
      exact hkeyEq
  exact hprefixEffect.append childEffect

end Weth10

end Blanc
