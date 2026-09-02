import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface
import Blanc.LidoTriggerableWithdrawalsGatewayRoleRoute

/-!
# Exact successful `pauseFor` execution

This unit starts at the actual compiled program entry and follows the selected
`pauseFor` body through every source guard.  Reverting arms are eliminated by
compiled-walk inversion; neither an evaluator result nor an assumed body walk
appears in the theorem statement.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

private theorem panic_call_not_ok
    {dp : DeployParams} {e : Sevm} {pre post : Devm}
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      e pre (.call arithmeticPanicSlot) (.ok post)) : False := by
  have hget : ((runtime dp).main :: (runtime dp).aux)[arithmeticPanicSlot]? =
      some (Func.revertData ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++
        (Nat.toB256 0x11).toBytes)) := by
    simp [runtime, aux, baseAux, arithmeticPanicSlot]
  exact Func.RunCompiledTo.not_ok_call_revertData hget run

private theorem pauseForSentinel_effect
    {dp : DeployParams} {e : Sevm} {root pre post : Devm}
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      e pre pauseForSentinel (.ok post)) :
    post.getStorVal e.currentTarget resumeSinceSlot = pauseInfinitely := by
  unfold pauseForSentinel at run
  obtain ⟨stopPre, lineRun, stopRun⟩ := runCompiledTo_prepend_inv run
  rcases Line.of_run_cons lineRun with ⟨s1, qvalue, lineRun⟩
  rcases Line.of_run_cons lineRun with ⟨storePre, qslot, lineRun⟩
  rcases Line.of_run_cons lineRun with ⟨storePost, qstore, eventRun⟩
  have p1 := prefix_of_push (of_run_pushB256 qvalue) hp
  have p2 := prefix_of_push (of_run_pushB256 qslot) p1
  have storeEffect := sstore_getStor_set qstore p2
  have eventStor : Devm.getStor storePost = Devm.getStor stopPre :=
    Line.of_inv Devm.getStor (by line_inv) eventRun
  have hpost : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
  rw [hpost]
  change (Devm.getStor stopPre e.currentTarget).get resumeSinceSlot =
    pauseInfinitely
  rw [← congrFun eventStor e.currentTarget, storeEffect,
    Stor.get_set_self]

private theorem pauseForFinite_effect
    {dp : DeployParams} {e : Sevm} {root pre post : Devm}
    {duration : B256}
    (harg : Sevm.argWord e 0 = duration)
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      e pre pauseForFinite (.ok post)) :
    post.getStorVal e.currentTarget resumeSinceSlot =
      duration + e.benvStat.time := by
  unfold pauseForFinite at run
  obtain ⟨testPost, testRun, branchRun⟩ := runCompiledTo_prepend_inv run
  have testStor : Devm.getStor pre = Devm.getStor testPost :=
    Line.of_inv Devm.getStor (by line_inv) testRun
  rcases Line.of_run_cons testRun with ⟨s1, qtime1, testRun⟩
  have p1 := prefix_of_timestamp hp qtime1
  unfold arg cdl at testRun
  rcases Line.of_run_cons testRun with ⟨argPush, qargPush, testRun⟩
  rcases Line.of_run_cons testRun with ⟨s2, qargLoad, testRun⟩
  rcases Line.of_run_cons testRun with ⟨s3, qadd, testRun⟩
  rcases Line.of_run_cons testRun with ⟨s4, qdup, testRun⟩
  rcases Line.of_run_cons testRun with ⟨s5, qtime2, testRun⟩
  rcases Line.of_run_cons testRun with ⟨_, qgt, hnil⟩
  cases hnil
  have p2a := prefix_of_push (of_run_pushB256 qargPush) p1
  have p2 := prefix_of_calldataload_val qargLoad p2a
  change Sevm.argWord e 0 :: e.benvStat.time :: ([] : Stack) <<+
    s2.stack at p2
  rw [harg] at p2
  have p3 := prefix_of_add qadd p2
  have p4 := prefix_of_dup_val qdup (by show_nth) p3
  have p5 := prefix_of_timestamp p4 qtime2
  have p6 := prefix_of_gt qgt p5
  obtain ⟨writePre, hpop, writeRun, psum⟩ : ∃ writePre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) testPost writePre ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) e writePre
        (([Ninst.pushB256 resumeSinceSlot, Ninst.sstore] ++ arg 0 ++
          mstoreAt 0 ++
          [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop) (.ok post) ∧
      (duration + e.benvStat.time) :: ([] : Stack) <<+ writePre.stack := by
    rcases runCompiledTo_branch_inv branchRun with hzero | hsucc
    · rcases hzero with ⟨writePre, hstack, hpop, writeRun⟩
      have hflag : (e.benvStat.time >? (duration + e.benvStat.time)) = 0 := by
        have pzero : (0 : B256) :: ([] : Stack) <<+ testPost.stack :=
          ⟨writePre.stack, by simpa [Split] using hstack⟩
        exact pref_head_unique p6 pzero
      have p6' : (0 : B256) :: (duration + e.benvStat.time) ::
          ([] : Stack) <<+ testPost.stack := by simpa [hflag] using p6
      exact ⟨writePre, hpop, writeRun,
        (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) p6').2⟩
    · rcases hsucc with ⟨_, _, _, -, -, panicRun⟩
      exact (panic_call_not_ok panicRun).elim
  obtain ⟨stopPre, writeLine, stopRun⟩ := runCompiledTo_prepend_inv writeRun
  rcases Line.of_run_cons writeLine with ⟨storePre, qslot, writeLine⟩
  rcases Line.of_run_cons writeLine with ⟨storePost, qstore, eventRun⟩
  have pslot := prefix_of_push (of_run_pushB256 qslot) psum
  have storeEffect := sstore_getStor_set qstore pslot
  have beforeWriteStor : Devm.getStor root = Devm.getStor writePre :=
    hstor.trans (testStor.trans
      (funext (getStor_eq_of_state_eq hpop.state)))
  have eventStor : Devm.getStor storePost = Devm.getStor stopPre :=
    Line.of_inv Devm.getStor (by line_inv) eventRun
  have hpost : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
  rw [hpost]
  change (Devm.getStor stopPre e.currentTarget).get resumeSinceSlot =
    duration + e.benvStat.time
  rw [← congrFun eventStor e.currentTarget, storeEffect,
    Stor.get_set_self]

/-! Exact traversal of the checked body selected after `onlyRole`. -/

private theorem pauseForGuard_effect
    {dp : DeployParams} {sevm : Sevm} {root pre post : Devm}
    {duration : B256}
    (harg : Sevm.argWord sevm 0 = duration)
    (hstor : Devm.getStor root = Devm.getStor pre)
    (hp : ([] : Stack) <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot)) (.ok post)) :
    post.getStorVal sevm.currentTarget resumeSinceSlot =
      Blanc.pauseForProjection sevm.benvStat.time duration := by
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
  obtain ⟨resumeSince, pLoad, -⟩ := prefix_of_sload qload pSlot
  have pTime := prefix_of_timestamp pLoad qtime
  have pLt := prefix_of_lt qlt pTime
  have pGuard := prefix_of_iszero qzero pLt
  obtain ⟨unpausedPre, unpausedRun, pUnpaused, guardPopStor⟩ :
      ∃ unpausedPre,
        Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
          sevm unpausedPre pauseForUnpaused (.ok post) ∧
        ([] : Stack) <<+ unpausedPre.stack ∧
        Devm.getStor guardTest = Devm.getStor unpausedPre := by
    rcases runCompiledTo_branch_inv guardBranch with hzero | hsucc
    · rcases hzero with ⟨_, -, -, errorRun⟩
      have hget :
          ((runtime dp).main :: (runtime dp).aux)[resumedExpectedSlot]? =
            some (runtimeError "ResumedExpected") := by
        simp [runtime, aux, baseAux, resumedExpectedSlot]
      exact (Func.RunCompiledTo.not_ok_call_revertSelector
        (by simpa [runtimeError] using hget) errorRun).elim
    · rcases hsucc with
        ⟨word, unpausedPre, -, hstack, hpop, unpausedRun⟩
      have pWord : word :: ([] : Stack) <<+ guardTest.stack :=
        ⟨unpausedPre.stack, by simpa [Split] using hstack⟩
      have hflag := pref_head_unique pGuard pWord
      have pFlag : word :: ([] : Stack) <<+ guardTest.stack := by
        simpa [hflag] using pGuard
      exact ⟨unpausedPre, unpausedRun,
        (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pFlag).2,
        funext (getStor_eq_of_state_eq hpop.state)⟩
  have unpausedStor : Devm.getStor root = Devm.getStor unpausedPre :=
    hstor.trans (guardLineStor.trans guardPopStor)

  unfold pauseForUnpaused at unpausedRun
  obtain ⟨durationTest, durationLine, durationBranch⟩ :=
    runCompiledTo_prepend_inv unpausedRun
  have durationLineStor : Devm.getStor unpausedPre = Devm.getStor durationTest :=
    Line.of_inv Devm.getStor (by line_inv) durationLine
  unfold arg cdl at durationLine
  rcases Line.of_run_cons durationLine with
    ⟨durationArgPush, qdurationArgPush, durationLine⟩
  rcases Line.of_run_cons durationLine with
    ⟨afterDurationArg, qdurationArgLoad, durationLine⟩
  rcases Line.of_run_cons durationLine with ⟨_, qdurationZero, hnil⟩
  cases hnil
  have pD1 := prefix_of_push
    (of_run_pushB256 qdurationArgPush) pUnpaused
  have pD2 := prefix_of_calldataload_val qdurationArgLoad pD1
  change Sevm.argWord sevm 0 :: ([] : Stack) <<+
    afterDurationArg.stack at pD2
  rw [harg] at pD2
  have pDurationTest := prefix_of_iszero qdurationZero pD2
  obtain ⟨sentinelTestPre, sentinelTestRun, pSentinelTest,
      durationPopStor, durationNonzero⟩ :
      ∃ sentinelTestPre,
        Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
          sevm sentinelTestPre
            ((arg 0 ++ [Ninst.pushB256 pauseInfinitely, Ninst.eq]) +++
              (pauseForSentinel <?> pauseForFinite)) (.ok post) ∧
        ([] : Stack) <<+ sentinelTestPre.stack ∧
        Devm.getStor durationTest = Devm.getStor sentinelTestPre ∧
        duration ≠ 0 := by
    rcases runCompiledTo_branch_inv durationBranch with hzero | hsucc
    · rcases hzero with ⟨sentinelTestPre, hstack, hpop, testRun⟩
      have pZero : (0 : B256) :: ([] : Stack) <<+ durationTest.stack :=
        ⟨sentinelTestPre.stack, by simpa [Split] using hstack⟩
      have hflag : (duration =? 0) = 0 :=
        pref_head_unique pDurationTest pZero
      have durationNonzero : duration ≠ 0 := by
        intro hz
        subst duration
        simp [B256.eqCheck, hz] at hflag
        exact absurd hflag (by decide)
      have pFlag : (0 : B256) :: ([] : Stack) <<+ durationTest.stack := by
        simpa [hflag] using pDurationTest
      exact ⟨sentinelTestPre, testRun,
        (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pFlag).2,
        funext (getStor_eq_of_state_eq hpop.state), durationNonzero⟩
    · rcases hsucc with ⟨_, _, -, -, -, errorRun⟩
      have hget :
          ((runtime dp).main :: (runtime dp).aux)[zeroPauseDurationSlot]? =
            some (runtimeError "ZeroPauseDuration") := by
        simp [runtime, aux, baseAux, zeroPauseDurationSlot]
      exact (Func.RunCompiledTo.not_ok_call_revertSelector
        (by simpa [runtimeError] using hget) errorRun).elim
  have sentinelTestStor :
      Devm.getStor root = Devm.getStor sentinelTestPre :=
    unpausedStor.trans (durationLineStor.trans durationPopStor)

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
    have hflag : (pauseInfinitely =? duration) = 0 :=
      pref_head_unique pEq pZero
    have finiteDuration : duration ≠ pauseInfinitely := by
      intro heq
      subst duration
      simp [B256.eqCheck, heq] at hflag
      exact absurd hflag (by decide)
    have pFlag : (0 : B256) :: ([] : Stack) <<+ sentinelBranch.stack := by
      simpa [hflag] using pEq
    have pFinite :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pFlag).2
    have finiteStor : Devm.getStor root = Devm.getStor finitePre :=
      sentinelTestStor.trans (sentinelLineStor.trans
        (funext (getStor_eq_of_state_eq hpop.state)))
    have effect := pauseForFinite_effect harg finiteStor pFinite finiteRun
    calc
      post.getStorVal sevm.currentTarget resumeSinceSlot =
          duration + sevm.benvStat.time := effect
      _ = sevm.benvStat.time + duration := B256.add_comm
      _ = (if duration = pauseInfinitely then pauseInfinitely
          else sevm.benvStat.time + duration) := by simp [finiteDuration]
      _ = Blanc.pauseForProjection sevm.benvStat.time duration :=
        pauseFor_projection_eq _ _
  · rcases hsentinel with
      ⟨word, sentinelPre, hword, hstack, hpop, sentinelRun⟩
    have pWord : word :: ([] : Stack) <<+ sentinelBranch.stack :=
      ⟨sentinelPre.stack, by simpa [Split] using hstack⟩
    have hflag : (pauseInfinitely =? duration) = word :=
      pref_head_unique pEq pWord
    have durationSentinel : duration = pauseInfinitely := by
      by_contra hne
      have hzero : (pauseInfinitely =? duration) = 0 := by
        simp [B256.eqCheck, Ne.symm hne]
      exact hword (hflag.symm.trans hzero)
    have pFlag : word :: ([] : Stack) <<+ sentinelBranch.stack := by
      simpa [hflag] using pEq
    have pSentinel :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) pFlag).2
    have sentinelStor : Devm.getStor root = Devm.getStor sentinelPre :=
      sentinelTestStor.trans (sentinelLineStor.trans
        (funext (getStor_eq_of_state_eq hpop.state)))
    have effect := pauseForSentinel_effect sentinelStor pSentinel sentinelRun
    calc
      post.getStorVal sevm.currentTarget resumeSinceSlot = pauseInfinitely :=
        effect
      _ = (if duration = pauseInfinitely then pauseInfinitely
          else sevm.benvStat.time + duration) := by simp [durationSentinel]
      _ = Blanc.pauseForProjection sevm.benvStat.time duration :=
        pauseFor_projection_eq _ _

/-- A successful exact `pauseFor` entry proves both the caller's role record
and the precise `resumeSinceSlot` write, including the infinite sentinel. -/
theorem pauseFor_ok_authorized_effect
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm} {duration : B256}
    (run : Prog.RunCompiledTo sevm pre (runtime dp) (.ok post))
    (hstack : pre.stack = [])
    (hdata : sevm.data = pauseForCalldata duration) :
    sevm.value = 0 ∧
      CallerHasRole (Devm.getStor pre sevm.currentTarget)
        pauseRole sevm.caller.toB256 ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot =
        Blanc.pauseForProjection sevm.benvStat.time duration := by
  have hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0 := by
    rw [hdata, pauseForCalldata_length]
    decide
  have hselector : Sevm.selector sevm = selPauseFor := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selPauseFor) (tail := duration.toBytes)
    · rfl
    · simpa [pauseForCalldata] using hdata
  have hmember : (selPauseFor, nonpayable pauseFor) ∈ funcs dp := by
    simp [funcs]
  obtain ⟨bodyPre, bodyRun, hbodyStack, hentryFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame run hstack hguard hselector hmember
  have pBody : ([] : Stack) <<+ bodyPre.stack := by
    rw [hbodyStack]
    exact nil_pref
  have rootStor : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq hentryFrame.state)
  have harg : Sevm.argWord sevm 0 = duration := by
    apply dataWord_of_append
      (pre := abiSelectorBytes selPauseFor) (post := [])
    · rw [abiSelectorBytes_length]
      rfl
    · simpa [pauseForCalldata] using hdata

  obtain ⟨valueZero, pausePre, pauseRun, pPause, wrapperStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_ok pBody bodyRun

  have staticGuard : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * 1)) = 0 := by
    rw [hdata, pauseForCalldata_length]
    decide
  unfold pauseFor at pauseRun
  obtain ⟨onlyRolePre, onlyRoleRun, pOnlyRole, staticStor⟩ :=
    requireStaticArgs_body_of_sufficient_calldata
      pPause staticGuard pauseRun
  have onlyRoleStor : Devm.getStor pre = Devm.getStor onlyRolePre :=
    rootStor.trans (wrapperStor.trans staticStor)

  obtain ⟨pauseGuardPre, authorizedAtRole, pauseGuardRun,
      pPauseGuard, roleStor⟩ :=
    onlyRole_body_of_ok pOnlyRole onlyRoleRun
  have pauseGuardStor : Devm.getStor pre = Devm.getStor pauseGuardPre :=
    onlyRoleStor.trans roleStor
  have authorized : CallerHasRole (Devm.getStor pre sevm.currentTarget)
      pauseRole sevm.caller.toB256 := by
    rw [congrFun onlyRoleStor sevm.currentTarget]
    exact authorizedAtRole
  have effect :=
    pauseForGuard_effect harg pauseGuardStor pPauseGuard pauseGuardRun
  exact ⟨valueZero, authorized, effect⟩

end LidoTriggerableWithdrawalsGateway
end Blanc
