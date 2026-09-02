import Blanc.LidoTriggerableWithdrawalsGatewayRoleRoute

/-!
# Exact `pauseUntil` and `resume` execution

This unit starts at an actual successful compiled runtime entry and follows the
selected nonpayable endpoint through its role gate and source body.  The
`pauseUntil` proof distinguishes the sentinel arm from the checked finite arm;
the latter writes `expiry + 1`, matching the inclusive Solidity deadline.  The
`resume` proof writes the current timestamp.  No evaluator result or assumed
body walk appears in the public statements.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway

/-- Exact calldata for `pauseUntil(uint256)`. -/
def pauseUntilCalldata (expiry : B256) : Bytes :=
  abiSelectorBytes selPauseUntil ++ expiry.toBytes

/-- Exact calldata for `resume()`. -/
def resumeCalldata : Bytes :=
  abiSelectorBytes selResume

theorem pauseUntilCalldata_length (expiry : B256) :
    (pauseUntilCalldata expiry).length = 36 := by
  simp [pauseUntilCalldata, abiSelectorBytes_length, B256.length_toBytes]

theorem resumeCalldata_length : resumeCalldata.length = 4 := by
  simp [resumeCalldata, abiSelectorBytes_length]

/-! Exact write effects for the two `pauseUntil` terminal arms. -/

private theorem pauseUntilSentinel_effect
    {dp : DeployParams} {sevm : Sevm} {root pre post : Devm}
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre pauseUntilSentinel (.ok post)) :
    post.getStorVal sevm.currentTarget resumeSinceSlot = pauseInfinitely := by
  unfold pauseUntilSentinel at run
  obtain ⟨stopPre, lineRun, stopRun⟩ := runCompiledTo_prepend_inv run
  rcases Line.of_run_cons lineRun with ⟨afterValue, qvalue, lineRun⟩
  rcases Line.of_run_cons lineRun with ⟨storePre, qslot, lineRun⟩
  rcases Line.of_run_cons lineRun with ⟨storePost, qstore, eventRun⟩
  have p1 := prefix_of_push (of_run_pushB256 qvalue) hp
  have p2 := prefix_of_push (of_run_pushB256 qslot) p1
  have storeEffect := sstore_getStor_set qstore p2
  have eventStor : Devm.getStor storePost = Devm.getStor stopPre :=
    Line.of_inv Devm.getStor (by line_inv) eventRun
  have postEq : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
  rw [postEq]
  change (Devm.getStor stopPre sevm.currentTarget).get resumeSinceSlot =
    pauseInfinitely
  rw [← congrFun eventStor sevm.currentTarget, storeEffect,
    Stor.get_set_self]

private theorem pauseUntilFinite_effect
    {dp : DeployParams} {sevm : Sevm} {root pre post : Devm}
    {expiry : B256}
    (harg : Sevm.argWord sevm 0 = expiry)
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre pauseUntilFinite (.ok post)) :
    post.getStorVal sevm.currentTarget resumeSinceSlot = expiry + 1 := by
  unfold pauseUntilFinite at run
  obtain ⟨testPre, testRun, branchRun⟩ := runCompiledTo_prepend_inv run
  have testStor : Devm.getStor pre = Devm.getStor testPre :=
    Line.of_inv Devm.getStor (by line_inv) testRun
  unfold arg cdl at testRun
  rcases Line.of_run_cons testRun with ⟨argPush, qargPush, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterArg, qargLoad, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterOne, qone, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterAdd, qadd, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterDup, qdup, testRun⟩
  rcases Line.of_run_cons testRun with ⟨argPushAgain, qargPushAgain, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterArgAgain, qargLoadAgain, testRun⟩
  rcases Line.of_run_cons testRun with ⟨_, qgt, hnil⟩
  cases hnil
  have p1a := prefix_of_push (of_run_pushB256 qargPush) hp
  have p1 := prefix_of_calldataload_val qargLoad p1a
  change Sevm.argWord sevm 0 :: ([] : Stack) <<+ afterArg.stack at p1
  rw [harg] at p1
  have p2 := prefix_of_push (of_run_pushB256 qone) p1
  have p3a := prefix_of_add qadd p2
  have p3 : (expiry + 1) :: ([] : Stack) <<+ afterAdd.stack := by
    simpa only [B256.add_comm] using p3a
  have p4 := prefix_of_dup_val qdup (by show_nth) p3
  have p5a := prefix_of_push (of_run_pushB256 qargPushAgain) p4
  have p5 := prefix_of_calldataload_val qargLoadAgain p5a
  change Sevm.argWord sevm 0 :: (expiry + 1) :: (expiry + 1) ::
    ([] : Stack) <<+ afterArgAgain.stack at p5
  rw [harg] at p5
  have p6 := prefix_of_gt qgt p5
  obtain ⟨writePre, hpop, writeRun, pSum⟩ : ∃ writePre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) testPre writePre ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm writePre
          (([dup 0] ++ mstoreAt 1 ++
            [pushB256 resumeSinceSlot, sstore] ++ mloadWord 1 ++
            [timestamp, swap 0, sub] ++ mstoreAt 0 ++
            [pushB256 (signatureHash "Paused" [.uint256])] ++
            logWith 0 0 1) +++ Func.stop) (.ok post) ∧
      (expiry + 1) :: ([] : Stack) <<+ writePre.stack := by
    rcases runCompiledTo_branch_inv branchRun with hzero | hsucc
    · rcases hzero with ⟨writePre, hstack, hpop, writeRun⟩
      have pZero : (0 : B256) :: ([] : Stack) <<+ testPre.stack :=
        ⟨writePre.stack, by simpa [Split] using hstack⟩
      have hflag : (expiry >? (expiry + 1)) = 0 :=
        pref_head_unique p6 pZero
      have p6' : (0 : B256) :: (expiry + 1) :: ([] : Stack) <<+
          testPre.stack := by simpa [hflag] using p6
      exact ⟨writePre, hpop, writeRun,
        (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) p6').2⟩
    · rcases hsucc with ⟨_, _, _, -, -, panicRun⟩
      have hget :
          ((runtime dp).main :: (runtime dp).aux)[arithmeticPanicSlot]? =
            some (Func.revertData
              ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++
                (Nat.toB256 0x11).toBytes)) := by
        simp [runtime, aux, baseAux, arithmeticPanicSlot]
      exact (Func.RunCompiledTo.not_ok_call_revertData hget panicRun).elim
  obtain ⟨stopPre, writeLine, stopRun⟩ :=
    runCompiledTo_prepend_inv writeRun
  rcases of_run_append [dup 0] writeLine with
    ⟨afterDupWrite, dupRun, writeLine⟩
  rcases of_run_append (mstoreAt 1) writeLine with
    ⟨afterMemory, memoryRun, writeLine⟩
  rcases Line.of_run_cons writeLine with ⟨storePre, qslot, writeLine⟩
  rcases Line.of_run_cons writeLine with ⟨storePost, qstore, eventRun⟩
  rcases Line.of_run_cons dupRun with ⟨_, qdupWrite, dupNil⟩
  cases dupNil
  have pDup := prefix_of_dup_val qdupWrite (by show_nth) pSum
  have pAfterMemory := (of_run_mstoreAt_val memoryRun pDup).1
  have pSlot := prefix_of_push (of_run_pushB256 qslot) pAfterMemory
  have storeEffect := sstore_getStor_set qstore pSlot
  have beforeWriteStor : Devm.getStor root = Devm.getStor writePre :=
    hstor.trans (testStor.trans
      (funext (getStor_eq_of_state_eq hpop.state)))
  have eventStor : Devm.getStor storePost = Devm.getStor stopPre :=
    Line.of_inv Devm.getStor (by line_inv) eventRun
  have postEq : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
  rw [postEq]
  change (Devm.getStor stopPre sevm.currentTarget).get resumeSinceSlot =
    expiry + 1
  rw [← congrFun eventStor sevm.currentTarget, storeEffect,
    Stor.get_set_self]

/-! The exact checked body selected after `onlyRole`. -/

private theorem pauseUntilGuard_effect
    {dp : DeployParams} {sevm : Sevm} {root pre post : Devm}
    {expiry : B256}
    (harg : Sevm.argWord sevm 0 = expiry)
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (([pushB256 resumeSinceSlot, sload, timestamp, lt, iszero]) +++
          (pauseUntilUnpaused <?> .call resumedExpectedSlot)) (.ok post)) :
    ¬ sevm.benvStat.time <
        root.getStorVal sevm.currentTarget resumeSinceSlot ∧
      ¬ expiry < sevm.benvStat.time ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot =
        pauseUntilSourceProjection sevm.benvStat.time expiry := by
  obtain ⟨guardTest, guardLine, guardBranch⟩ :=
    runCompiledTo_prepend_inv run
  have guardLineStor : Devm.getStor pre = Devm.getStor guardTest :=
    Line.of_inv Devm.getStor (by line_inv) guardLine
  rcases Line.of_run_cons guardLine with ⟨afterSlot, qslot, guardLine⟩
  rcases Line.of_run_cons guardLine with ⟨afterLoad, qload, guardLine⟩
  rcases Line.of_run_cons guardLine with ⟨afterTime, qtime, guardLine⟩
  rcases Line.of_run_cons guardLine with ⟨afterLt, qlt, guardLine⟩
  rcases Line.of_run_cons guardLine with ⟨_, qzero, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨resumeSince, pLoad, resumeRead⟩ := prefix_of_sload qload pSlot
  have pTime := prefix_of_timestamp pLoad qtime
  have pLt := prefix_of_lt qlt pTime
  have pGuard := prefix_of_iszero qzero pLt
  have slotStor : Devm.getStor pre = Devm.getStor afterSlot :=
    Ninst.Hinv.inv (f := Devm.getStor) qslot
  have resumeAtRoot : resumeSince =
      root.getStorVal sevm.currentTarget resumeSinceSlot := by
    rw [resumeRead]
    change (Devm.getStor afterSlot sevm.currentTarget).get resumeSinceSlot =
      (Devm.getStor root sevm.currentTarget).get resumeSinceSlot
    rw [← congrFun slotStor sevm.currentTarget,
      ← congrFun hstor sevm.currentTarget]
  rw [resumeAtRoot] at pGuard
  obtain ⟨unpausedPre, guardWord, hguardWord, hguardPop,
      unpausedRun, pUnpaused, guardFlag⟩ : ∃ unpausedPre guardWord,
      guardWord ≠ 0 ∧
      Devm.PopBurnBy [guardWord] (gVerylow + gHigh + gJumpdest)
        guardTest unpausedPre ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm unpausedPre pauseUntilUnpaused (.ok post) ∧
      ([] : Stack) <<+ unpausedPre.stack ∧
      ((sevm.benvStat.time <?
          root.getStorVal sevm.currentTarget resumeSinceSlot) =? 0) =
        guardWord := by
    rcases runCompiledTo_branch_inv guardBranch with hzero | hsucc
    · rcases hzero with ⟨_, -, -, errorRun⟩
      have hget :
          ((runtime dp).main :: (runtime dp).aux)[resumedExpectedSlot]? =
            some (runtimeError "ResumedExpected") := by
        simp [runtime, aux, baseAux, resumedExpectedSlot]
      exact (Func.RunCompiledTo.not_ok_call_revertSelector
        (by simpa [runtimeError] using hget) errorRun).elim
    · rcases hsucc with
        ⟨guardWord, unpausedPre, hnz, hstack, hpop, unpausedRun⟩
      have pWord : guardWord :: ([] : Stack) <<+ guardTest.stack :=
        ⟨unpausedPre.stack, by simpa [Split] using hstack⟩
      have hflag := pref_head_unique pGuard pWord
      have pFlag : guardWord :: ([] : Stack) <<+ guardTest.stack := by
        simpa [hflag] using pGuard
      exact ⟨unpausedPre, guardWord, hnz, hpop, unpausedRun,
        (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pFlag).2, hflag⟩
  have guardCheckNonzero :
      ((sevm.benvStat.time <?
          root.getStorVal sevm.currentTarget resumeSinceSlot) =? 0) ≠ 0 := by
    intro hz
    exact hguardWord (guardFlag.symm.trans hz)
  have entryUnpaused :
      ¬ sevm.benvStat.time <
        root.getStorVal sevm.currentTarget resumeSinceSlot := by
    intro hlt
    have hz :
        ((sevm.benvStat.time <?
            root.getStorVal sevm.currentTarget resumeSinceSlot) =? 0) = 0 := by
      simp [B256.ltCheck, hlt, B256.eqCheck]
    exact guardCheckNonzero hz
  have unpausedStor : Devm.getStor root = Devm.getStor unpausedPre :=
    hstor.trans (guardLineStor.trans
      (funext (getStor_eq_of_state_eq hguardPop.state)))

  unfold pauseUntilUnpaused at unpausedRun
  obtain ⟨pastTest, pastLine, pastBranch⟩ :=
    runCompiledTo_prepend_inv unpausedRun
  have pastLineStor : Devm.getStor unpausedPre = Devm.getStor pastTest :=
    Line.of_inv Devm.getStor (by line_inv) pastLine
  rcases Line.of_run_cons pastLine with ⟨afterTime2, qtime2, pastLine⟩
  have pTime2 := prefix_of_timestamp pUnpaused qtime2
  unfold arg cdl at pastLine
  rcases Line.of_run_cons pastLine with ⟨argPush, qargPush, pastLine⟩
  rcases Line.of_run_cons pastLine with ⟨afterArg, qargLoad, pastLine⟩
  rcases Line.of_run_cons pastLine with ⟨_, qpast, hnil⟩
  cases hnil
  have pArg0 := prefix_of_push (of_run_pushB256 qargPush) pTime2
  have pArg := prefix_of_calldataload_val qargLoad pArg0
  change Sevm.argWord sevm 0 :: sevm.benvStat.time ::
    ([] : Stack) <<+ afterArg.stack at pArg
  rw [harg] at pArg
  have pPast := prefix_of_lt qpast pArg
  obtain ⟨sentinelTestPre, hpastPop, sentinelTestRun,
      pSentinelTest, expiryNotPast⟩ : ∃ sentinelTestPre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) pastTest sentinelTestPre ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm sentinelTestPre
          ((arg 0 ++ [pushB256 pauseInfinitely, eq]) +++
            (pauseUntilSentinel <?> pauseUntilFinite)) (.ok post) ∧
      ([] : Stack) <<+ sentinelTestPre.stack ∧
      ¬ expiry < sevm.benvStat.time := by
    rcases runCompiledTo_branch_inv pastBranch with hzero | hsucc
    · rcases hzero with ⟨sentinelTestPre, hstack, hpop, testRun⟩
      have pZero : (0 : B256) :: ([] : Stack) <<+ pastTest.stack :=
        ⟨sentinelTestPre.stack, by simpa [Split] using hstack⟩
      have hflag : (expiry <? sevm.benvStat.time) = 0 :=
        pref_head_unique pPast pZero
      have pPast' : (0 : B256) :: ([] : Stack) <<+ pastTest.stack := by
        simpa [hflag] using pPast
      have hnot : ¬ expiry < sevm.benvStat.time := by
        intro hpast
        rw [B256.ltCheck, if_pos hpast] at hflag
        exact (by decide : (1 : B256) ≠ 0) hflag
      exact ⟨sentinelTestPre, hpop, testRun,
        (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pPast').2, hnot⟩
    · rcases hsucc with ⟨_, _, _, -, -, errorRun⟩
      have hget :
          ((runtime dp).main :: (runtime dp).aux)[pauseUntilPastSlot]? =
            some (runtimeError "PauseUntilMustBeInFuture") := by
        simp [runtime, aux, baseAux, pauseUntilPastSlot]
      exact (Func.RunCompiledTo.not_ok_call_revertSelector
        (by simpa [runtimeError] using hget) errorRun).elim
  have sentinelTestStor :
      Devm.getStor root = Devm.getStor sentinelTestPre :=
    unpausedStor.trans (pastLineStor.trans
      (funext (getStor_eq_of_state_eq hpastPop.state)))

  obtain ⟨sentinelBranch, sentinelLine, sentinelBranchRun⟩ :=
    runCompiledTo_prepend_inv sentinelTestRun
  have sentinelLineStor :
      Devm.getStor sentinelTestPre = Devm.getStor sentinelBranch :=
    Line.of_inv Devm.getStor (by line_inv) sentinelLine
  unfold arg cdl at sentinelLine
  rcases Line.of_run_cons sentinelLine with
    ⟨sentinelArgPush, qsentinelArgPush, sentinelLine⟩
  rcases Line.of_run_cons sentinelLine with
    ⟨afterSentinelArg, qsentinelArgLoad, sentinelLine⟩
  rcases Line.of_run_cons sentinelLine with
    ⟨afterSentinelWord, qsentinelWord, sentinelLine⟩
  rcases Line.of_run_cons sentinelLine with ⟨_, qeq, hnil⟩
  cases hnil
  have pS1 := prefix_of_push
    (of_run_pushB256 qsentinelArgPush) pSentinelTest
  have pS2 := prefix_of_calldataload_val qsentinelArgLoad pS1
  change Sevm.argWord sevm 0 :: ([] : Stack) <<+
    afterSentinelArg.stack at pS2
  rw [harg] at pS2
  have pS3 := prefix_of_push (of_run_pushB256 qsentinelWord) pS2
  have pEq := prefix_of_eq qeq pS3
  rcases runCompiledTo_branch_inv sentinelBranchRun with hfinite | hsentinel
  · rcases hfinite with ⟨finitePre, hstack, hpop, finiteRun⟩
    have pZero : (0 : B256) :: ([] : Stack) <<+ sentinelBranch.stack :=
      ⟨finitePre.stack, by simpa [Split] using hstack⟩
    have hflag : (pauseInfinitely =? expiry) = 0 :=
      pref_head_unique pEq pZero
    have finiteExpiry : expiry ≠ pauseInfinitely := by
      intro heq
      have hone : (pauseInfinitely =? expiry) = 1 := by
        simp [B256.eqCheck, heq]
      exact (by decide : (1 : B256) ≠ 0) (hone.symm.trans hflag)
    have pEq' : (0 : B256) :: ([] : Stack) <<+ sentinelBranch.stack := by
      simpa [hflag] using pEq
    have pFinite :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pEq').2
    have finiteStor : Devm.getStor root = Devm.getStor finitePre :=
      sentinelTestStor.trans (sentinelLineStor.trans
        (funext (getStor_eq_of_state_eq hpop.state)))
    have effect := pauseUntilFinite_effect harg finiteStor pFinite finiteRun
    exact ⟨entryUnpaused, expiryNotPast, by
      simpa [pauseUntilSourceProjection, finiteExpiry] using effect⟩
  · rcases hsentinel with
      ⟨word, sentinelPre, hword, hstack, hpop, sentinelRun⟩
    have pWord : word :: ([] : Stack) <<+ sentinelBranch.stack :=
      ⟨sentinelPre.stack, by simpa [Split] using hstack⟩
    have hflag : (pauseInfinitely =? expiry) = word :=
      pref_head_unique pEq pWord
    have expirySentinel : expiry = pauseInfinitely := by
      by_contra hne
      have hzero : (pauseInfinitely =? expiry) = 0 := by
        simp [B256.eqCheck, Ne.symm hne]
      exact hword (hflag.symm.trans hzero)
    have pFlag : word :: ([] : Stack) <<+ sentinelBranch.stack := by
      simpa [hflag] using pEq
    have pSentinel :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pFlag).2
    have sentinelStor : Devm.getStor root = Devm.getStor sentinelPre :=
      sentinelTestStor.trans (sentinelLineStor.trans
        (funext (getStor_eq_of_state_eq hpop.state)))
    have effect := pauseUntilSentinel_effect sentinelStor pSentinel sentinelRun
    exact ⟨entryUnpaused, expiryNotPast, by
      simpa [pauseUntilSourceProjection, expirySentinel] using effect⟩

/-! Public exact `pauseUntil` runtime theorems. -/

/-- A successful exact `pauseUntil(uint256)` runtime entry proves its role
authorization and writes the source's inclusive/sentinel projection. -/
theorem pauseUntil_ok_authorized_effect
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {expiry : B256}
    (run : Prog.RunCompiledTo sevm pre (runtime dp) (.ok post))
    (entryStack : pre.stack = [])
    (calldata : sevm.data = pauseUntilCalldata expiry) :
    sevm.value = 0 ∧
      CallerHasRole (Devm.getStor pre sevm.currentTarget)
        pauseRole sevm.caller.toB256 ∧
      ¬ sevm.benvStat.time <
        pre.getStorVal sevm.currentTarget resumeSinceSlot ∧
      ¬ expiry < sevm.benvStat.time ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot =
        pauseUntilSourceProjection sevm.benvStat.time expiry := by
  have guard :
      B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0 := by
    rw [calldata, pauseUntilCalldata_length]
    decide
  have selected : Sevm.selector sevm = selPauseUntil := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
        (selected := selPauseUntil) (tail := expiry.toBytes)
    · rfl
    · simpa [pauseUntilCalldata] using calldata
  have member : (selPauseUntil, nonpayable pauseUntil) ∈ funcs dp := by
    simp [funcs]
  obtain ⟨routePre, routeRun, routeStack, routeFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame run entryStack guard selected member
  have pRoute : ([] : Stack) <<+ routePre.stack := by
    rw [routeStack]
    exact nil_pref
  have entryRouteStor : Devm.getStor pre = Devm.getStor routePre :=
    funext (getStor_eq_of_state_eq routeFrame.state)
  obtain ⟨valueZero, pausePre, pauseRun, pPause, wrapperStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_ok pRoute routeRun
  have harg : Sevm.argWord sevm 0 = expiry := by
    apply dataWord_of_append
      (pre := abiSelectorBytes selPauseUntil) (post := [])
    · rw [abiSelectorBytes_length]
      rfl
    · simpa [pauseUntilCalldata] using calldata
  have staticGuard : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * 1)) = 0 := by
    rw [calldata, pauseUntilCalldata_length]
    decide
  unfold pauseUntil at pauseRun
  obtain ⟨onlyRolePre, onlyRoleRun, pOnlyRole, staticStor⟩ :=
    requireStaticArgs_body_of_sufficient_calldata
      pPause staticGuard pauseRun
  obtain ⟨guardPre, authorizedAtRole, guardRun, pGuard, roleStor⟩ :=
    onlyRole_body_of_ok pOnlyRole onlyRoleRun
  have entryRoleStor : Devm.getStor pre = Devm.getStor onlyRolePre :=
    entryRouteStor.trans (wrapperStor.trans staticStor)
  have authorized : CallerHasRole (Devm.getStor pre sevm.currentTarget)
      pauseRole sevm.caller.toB256 := by
    rw [congrFun entryRoleStor sevm.currentTarget]
    exact authorizedAtRole
  have entryGuardStor : Devm.getStor pre = Devm.getStor guardPre :=
    entryRoleStor.trans roleStor
  rcases pauseUntilGuard_effect harg entryGuardStor pGuard guardRun with
    ⟨entryUnpaused, expiryNotPast, effect⟩
  exact ⟨valueZero, authorized, entryUnpaused, expiryNotPast, effect⟩

/-- The sentinel call writes the sentinel itself. -/
theorem pauseUntil_sentinel_ok_authorized_effect
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiledTo sevm pre (runtime dp) (.ok post))
    (entryStack : pre.stack = [])
    (calldata : sevm.data = pauseUntilCalldata pauseInfinitely) :
    sevm.value = 0 ∧
      CallerHasRole (Devm.getStor pre sevm.currentTarget)
        pauseRole sevm.caller.toB256 ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = pauseInfinitely := by
  rcases pauseUntil_ok_authorized_effect run entryStack calldata with
    ⟨valueZero, authorized, -, -, effect⟩
  exact ⟨valueZero, authorized, by
    simpa [pauseUntilSourceProjection] using effect⟩

/-- Every non-sentinel call writes `expiry + 1`; this is the inclusive expiry
used by `isPaused`, whose comparison is strict. -/
theorem pauseUntil_finite_ok_authorized_effect
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {expiry : B256}
    (run : Prog.RunCompiledTo sevm pre (runtime dp) (.ok post))
    (entryStack : pre.stack = [])
    (calldata : sevm.data = pauseUntilCalldata expiry)
    (finite : expiry ≠ pauseInfinitely) :
    sevm.value = 0 ∧
      CallerHasRole (Devm.getStor pre sevm.currentTarget)
        pauseRole sevm.caller.toB256 ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = expiry + 1 := by
  rcases pauseUntil_ok_authorized_effect run entryStack calldata with
    ⟨valueZero, authorized, -, -, effect⟩
  exact ⟨valueZero, authorized, by
    simpa [pauseUntilSourceProjection, finite] using effect⟩

/-! Exact `resume` body and runtime theorem. -/

private theorem resumeSuccess_effect
    {dp : DeployParams} {sevm : Sevm} {root pre post : Devm}
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (([timestamp, pushB256 resumeSinceSlot, sstore] ++
          emitNoData (signatureHash "Resumed" [])) +++ Func.stop)
        (.ok post)) :
    post.getStorVal sevm.currentTarget resumeSinceSlot =
      resumeSourceProjection sevm.benvStat.time := by
  obtain ⟨stopPre, lineRun, stopRun⟩ := runCompiledTo_prepend_inv run
  rcases Line.of_run_cons lineRun with ⟨afterTime, qtime, lineRun⟩
  rcases Line.of_run_cons lineRun with ⟨storePre, qslot, lineRun⟩
  rcases Line.of_run_cons lineRun with ⟨storePost, qstore, eventRun⟩
  have pTime := prefix_of_timestamp hp qtime
  have pSlot := prefix_of_push (of_run_pushB256 qslot) pTime
  have storeEffect := sstore_getStor_set qstore pSlot
  have eventStor : Devm.getStor storePost = Devm.getStor stopPre :=
    Line.of_inv Devm.getStor (by line_inv) eventRun
  have postEq : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
  rw [postEq]
  change (Devm.getStor stopPre sevm.currentTarget).get resumeSinceSlot =
    sevm.benvStat.time
  rw [← congrFun eventStor sevm.currentTarget, storeEffect,
    Stor.get_set_self]

private theorem resumeGuard_effect
    {dp : DeployParams} {sevm : Sevm} {root pre post : Devm}
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (([pushB256 resumeSinceSlot, sload, timestamp, lt]) +++
          ((([timestamp, pushB256 resumeSinceSlot, sstore] ++
              emitNoData (signatureHash "Resumed" [])) +++ Func.stop)
            <?> .call pausedExpectedSlot)) (.ok post)) :
    sevm.benvStat.time <
        root.getStorVal sevm.currentTarget resumeSinceSlot ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot =
        resumeSourceProjection sevm.benvStat.time := by
  obtain ⟨guardTest, guardLine, guardBranch⟩ :=
    runCompiledTo_prepend_inv run
  have guardLineStor : Devm.getStor pre = Devm.getStor guardTest :=
    Line.of_inv Devm.getStor (by line_inv) guardLine
  rcases Line.of_run_cons guardLine with ⟨afterSlot, qslot, guardLine⟩
  rcases Line.of_run_cons guardLine with ⟨afterLoad, qload, guardLine⟩
  rcases Line.of_run_cons guardLine with ⟨afterTime, qtime, guardLine⟩
  rcases Line.of_run_cons guardLine with ⟨_, qlt, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨resumeSince, pLoad, resumeRead⟩ := prefix_of_sload qload pSlot
  have pTime := prefix_of_timestamp pLoad qtime
  have pGuard := prefix_of_lt qlt pTime
  have slotStor : Devm.getStor pre = Devm.getStor afterSlot :=
    Ninst.Hinv.inv (f := Devm.getStor) qslot
  have resumeAtRoot : resumeSince =
      root.getStorVal sevm.currentTarget resumeSinceSlot := by
    rw [resumeRead]
    change (Devm.getStor afterSlot sevm.currentTarget).get resumeSinceSlot =
      (Devm.getStor root sevm.currentTarget).get resumeSinceSlot
    rw [← congrFun slotStor sevm.currentTarget,
      ← congrFun hstor sevm.currentTarget]
  rw [resumeAtRoot] at pGuard
  obtain ⟨successPre, word, hword, hpop, successRun, pSuccess,
      guardFlag⟩ : ∃ successPre word,
      word ≠ 0 ∧
      Devm.PopBurnBy [word] (gVerylow + gHigh + gJumpdest)
        guardTest successPre ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm successPre
          (([timestamp, pushB256 resumeSinceSlot, sstore] ++
            emitNoData (signatureHash "Resumed" [])) +++ Func.stop)
          (.ok post) ∧
      ([] : Stack) <<+ successPre.stack ∧
      (sevm.benvStat.time <?
        root.getStorVal sevm.currentTarget resumeSinceSlot) = word := by
    rcases runCompiledTo_branch_inv guardBranch with hzero | hsucc
    · rcases hzero with ⟨_, -, -, errorRun⟩
      have hget :
          ((runtime dp).main :: (runtime dp).aux)[pausedExpectedSlot]? =
            some (runtimeError "PausedExpected") := by
        simp [runtime, aux, baseAux, pausedExpectedSlot]
      exact (Func.RunCompiledTo.not_ok_call_revertSelector
        (by simpa [runtimeError] using hget) errorRun).elim
    · rcases hsucc with ⟨word, successPre, hnz, hstack, hpop, successRun⟩
      have pWord : word :: ([] : Stack) <<+ guardTest.stack :=
        ⟨successPre.stack, by simpa [Split] using hstack⟩
      have hflag := pref_head_unique pGuard pWord
      have pFlag : word :: ([] : Stack) <<+ guardTest.stack := by
        simpa [hflag] using pGuard
      exact ⟨successPre, word, hnz, hpop, successRun,
        (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pFlag).2, hflag⟩
  have guardNonzero :
      (sevm.benvStat.time <?
        root.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0 := by
    intro hz
    exact hword (guardFlag.symm.trans hz)
  have paused : sevm.benvStat.time <
      root.getStorVal sevm.currentTarget resumeSinceSlot := by
    by_contra hnot
    have hz :
        (sevm.benvStat.time <?
          root.getStorVal sevm.currentTarget resumeSinceSlot) = 0 := by
      simp [B256.ltCheck, hnot]
    exact guardNonzero hz
  have successStor : Devm.getStor root = Devm.getStor successPre :=
    hstor.trans (guardLineStor.trans
      (funext (getStor_eq_of_state_eq hpop.state)))
  exact ⟨paused,
    resumeSuccess_effect successStor pSuccess successRun⟩

/-- A successful exact `resume()` runtime entry proves the caller's resume
role, proves that the entry state was paused, and writes `block.timestamp`. -/
theorem resume_ok_authorized_effect
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiledTo sevm pre (runtime dp) (.ok post))
    (entryStack : pre.stack = [])
    (calldata : sevm.data = resumeCalldata) :
    sevm.value = 0 ∧
      CallerHasRole (Devm.getStor pre sevm.currentTarget)
        resumeRole sevm.caller.toB256 ∧
      sevm.benvStat.time <
        pre.getStorVal sevm.currentTarget resumeSinceSlot ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot =
        sevm.benvStat.time := by
  have guard :
      B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0 := by
    rw [calldata, resumeCalldata_length]
    change B256.ltCheck (4 : B256) 4 = 0
    rw [B256.ltCheck, if_neg (lt_irrefl _)]
  have selected : Sevm.selector sevm = selResume := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
        (selected := selResume) (tail := [])
    · rfl
    · simpa [resumeCalldata] using calldata
  have member : (selResume, nonpayable resume) ∈ funcs dp := by
    simp [funcs]
  obtain ⟨routePre, routeRun, routeStack, routeFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame run entryStack guard selected member
  have pRoute : ([] : Stack) <<+ routePre.stack := by
    rw [routeStack]
    exact nil_pref
  have entryRouteStor : Devm.getStor pre = Devm.getStor routePre :=
    funext (getStor_eq_of_state_eq routeFrame.state)
  obtain ⟨valueZero, resumePre, resumeRun, pResume, wrapperStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_ok pRoute routeRun
  unfold resume at resumeRun
  obtain ⟨guardPre, authorizedAtRole, guardRun, pGuard, roleStor⟩ :=
    onlyRole_body_of_ok pResume resumeRun
  have entryRoleStor : Devm.getStor pre = Devm.getStor resumePre :=
    entryRouteStor.trans wrapperStor
  have authorized : CallerHasRole (Devm.getStor pre sevm.currentTarget)
      resumeRole sevm.caller.toB256 := by
    rw [congrFun entryRoleStor sevm.currentTarget]
    exact authorizedAtRole
  have entryGuardStor : Devm.getStor pre = Devm.getStor guardPre :=
    entryRoleStor.trans roleStor
  rcases resumeGuard_effect entryGuardStor pGuard guardRun with
    ⟨paused, effect⟩
  exact ⟨valueZero, authorized, paused, by
    simpa [resumeSourceProjection] using effect⟩

end LidoTriggerableWithdrawalsGateway
end Blanc
