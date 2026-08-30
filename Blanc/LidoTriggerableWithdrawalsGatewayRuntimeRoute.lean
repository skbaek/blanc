import Blanc.LidoTriggerableWithdrawalsGateway
import Blanc.LinearDispatchCorrectness

/-!
# Exact runtime-route seams for the Triggerable Withdrawals Gateway

This module keeps the A2 route boundary explicit.  `Prog.RunCompiledTo` is
unpacked to its exact entry burn and main walk, and the runtime's calldata
guard and `fsig` prefix are inverted before the dispatcher suffix is selected
by the shared kernel theorem.  No evaluator or `Nonempty` evidence is used.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

def CallerHasRole (stor : Stor) (role account : B256) : Prop :=
  lookupRecordMatches role account
    (stor.get (roleLookupRoleSlot role account))
    (stor.get (roleLookupAccountSlot role account))
    (stor.get (roleLookupIndexSlot role account))

/-- The concrete TWG selector table has no duplicate selectors. -/
theorem funcs_selector_unique (dp : DeployParams) : selectorUnique (funcs dp) := by
  simp [selectorUnique, funcs, selPauseFor, selIsPaused, selTriggerFullWithdrawals, selPauseRole, selResumeRole, selAddFullWithdrawalRequestRole, selTwExitLimitManagerRole, selTwrLimitPosition, selVersion, selResume, selPauseUntil, selSetExitRequestLimit, selGetExitRequestLimitFullInfo, selPauseInfinitely, selGetResumeSinceTimestamp, selDefaultAdminRole, selSupportsInterface, selHasRole, selGetRoleAdmin, selGrantRole, selRevokeRole, selRenounceRole, selGetRoleMember, selGetRoleMemberCount]
  repeat' apply And.intro
  all_goals decide +kernel

theorem callerHasRole_collision_refusal {stor : Stor}
    {role account storedRole storedAccount : B256}
    (hcollision : lookupCollision role account storedRole storedAccount)
    (hrole : stor.get (roleLookupRoleSlot role account) = storedRole)
    (haccount : stor.get (roleLookupAccountSlot role account) = storedAccount)
    (hcanonical : storedAccount = canonicalAccount storedAccount) :
    ¬ CallerHasRole stor role account := by
  intro h
  rcases h with ⟨_, hstoredRole, hstoredAccount⟩
  rcases hcollision.2 with hneq | hneq
  · exact hneq (hstoredRole.symm.trans hrole)
  · have heq : storedAccount = canonicalAccount account :=
      haccount.symm.trans hstoredAccount
    apply hneq
    calc
      canonicalAccount account = storedAccount := heq.symm
      _ = canonicalAccount storedAccount := hcanonical

theorem callerHasRole_exact_lookup {stor : Stor} {role account : B256}
    (hrole : stor.get (roleLookupRoleSlot role account) = role)
    (haccount : stor.get (roleLookupAccountSlot role account) =
      canonicalAccount account)
    (hindex : stor.get (roleLookupIndexSlot role account) ≠ 0) :
    CallerHasRole stor role account := by
  exact ⟨hindex, hrole, haccount⟩

/-! These are the source expressions computed by the finite/sentinel arms. -/

def pauseUntilSourceProjection (_timestamp expiry : B256) : B256 :=
  if expiry = pauseInfinitely then pauseInfinitely else expiry + 1

def resumeSourceProjection (timestamp : B256) : B256 := timestamp

theorem pauseUntilSourceProjection_sentinel (timestamp : B256) :
    pauseUntilSourceProjection timestamp pauseInfinitely = pauseInfinitely := by
  simp [pauseUntilSourceProjection]

theorem pauseUntilSourceProjection_finite {timestamp expiry : B256}
    (hfinite : expiry ≠ pauseInfinitely) :
    pauseUntilSourceProjection timestamp expiry = expiry + 1 := by
  simp [pauseUntilSourceProjection, hfinite]

theorem resumeSourceProjection_effect (timestamp : B256) :
    resumeSourceProjection timestamp = timestamp := rfl

/-! Exact compiled route packaging.  The dispatcher walk is obtained by
   inverting the program's own entry guard and selector prefix; it is not an
   extra premise disguised as a route witness. -/

private theorem prefix_head_eq {x : B256} {xs : Stack} {devm : Devm}
    (hp : x :: xs <<+ devm.stack) {w : B256} {rest : Stack}
    (hs : devm.stack = w :: rest) : x = w := by
  have hp' : (w :: []) <<+ devm.stack := ⟨rest, by simpa [Split] using hs⟩
  exact pref_head_unique hp hp'

theorem dispatcher_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector : B256} {body : Func}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selector)
    (huniq : selectorUnique (funcs dp))
    (hmember : (selector, body) ∈ funcs dp)
    : ∃ dispatchEntry tail,
        DispatchBodyWitness ((runtime dp).main :: (runtime dp).aux)
          sevm dispatchEntry (funcs dp) selector tail body out := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm mid
    ([Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] +++
      (Func.rev <?> (fsig +++ linearDispatchWith fallbackSlot (funcs dp)))) out
    at hmain
  obtain ⟨afterGuard, hguardRun, hbranch⟩ :=
    runCompiledTo_prepend_inv hmain
  rcases Line.of_run_cons hguardRun with ⟨afterPush, hpush, hrest⟩
  rcases Line.of_run_cons hrest with ⟨afterSize, hsize, hrest⟩
  rcases Line.of_run_cons hrest with ⟨afterLt, hlt, hnil⟩
  cases hnil
  have p1 : (4 : B256) :: [] <<+ afterPush.stack :=
    prefix_of_push (of_run_pushB256 hpush) nil_pref
  have p2 : sevm.data.length.toB256 :: (4 : B256) :: [] <<+ afterSize.stack :=
    prefix_of_push (of_run_calldatasize hsize) p1
  have p3 : (sevm.data.length.toB256 <? (4 : B256)) :: [] <<+ afterGuard.stack :=
    prefix_of_lt hlt p2
  have hflag : (sevm.data.length.toB256 <? (4 : B256)) = 0 := hguard
  have hzero : ∃ dispatchEntry,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm dispatchEntry
        (fsig +++ linearDispatchWith fallbackSlot (funcs dp)) out := by
    rcases runCompiledTo_branch_inv hbranch with hleft | hright
    · rcases hleft with ⟨armPre, hstack, hpop, harm⟩
      exact ⟨armPre, harm⟩
    · rcases hright with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hbad : (sevm.data.length.toB256 <? (4 : B256)) = w :=
        prefix_head_eq p3 hstack
      exact False.elim (hw (hbad.symm.trans hflag))
  obtain ⟨dispatchEntry, hzero⟩ := hzero
  obtain ⟨afterSig, hsig, hdispatch⟩ := runCompiledTo_prepend_inv hzero
  have psig : Sevm.selector sevm :: dispatchEntry.stack <<+ afterSig.stack :=
    prefix_of_fsig ⟨[], by simp [Split]⟩ hsig
  rw [hselector] at psig
  rcases psig with ⟨suffix, hstack⟩
  have hstack' : afterSig.stack = selector :: (dispatchEntry.stack ++ suffix) := by
    simpa [Split, List.cons_append] using hstack
  have hwitness := dispatchBodyWitness_of_runCompiledTo huniq hmember hstack'
    hdispatch
  exact ⟨afterSig, dispatchEntry.stack ++ suffix, hwitness⟩

/-! The exact-entry strengthening used by functional endpoint proofs.  Unlike
`dispatcher_body_of_prog_run`, this form starts with the program entry's empty
stack and carries the whole dispatch frame back to that entry. -/

private theorem runtimePrefix_dispatchFrame
    {entry mid afterGuard dispatchEntry afterSig : Devm}
    {sevm : Sevm}
    (hburn : Devm.BurnBy gJumpdest entry mid)
    (hguard : Line.Run sevm mid
      [Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] afterGuard)
    {word : B256} {cost : Nat}
    (hpop : Devm.PopBurnBy [word] cost afterGuard dispatchEntry)
    (hsig : Line.Run sevm dispatchEntry fsig afterSig) :
    Devm.DispatchFramePreserved entry afterSig := by
  rcases Line.of_run_cons hguard with ⟨guardPush, qpush4, hguard⟩
  rcases Line.of_run_cons hguard with ⟨guardSize, qsize, hguard⟩
  rcases Line.of_run_cons hguard with ⟨guardLt, qlt, hguardNil⟩
  cases hguardNil
  rcases of_run_reg qlt with ⟨_, qltCore⟩
  simp only [Rinst.run, Rinst.runCore] at qltCore
  rcases Devm.diffBurn_of_applyBinary qltCore with ⟨_, _, qltDiff⟩
  unfold fsig cdl shiftRight at hsig
  rcases Line.of_run_cons hsig with ⟨sigPush, qpush0, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigLoad, qload, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigShift, qpush224, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigDone, qshr, hsigNil⟩
  cases hsigNil
  rcases of_run_reg qload with ⟨_, qloadCore⟩
  simp only [Rinst.run, Rinst.runCore] at qloadCore
  rcases Except.bind_eq_ok qloadCore with ⟨⟨loadOffset, loadPop⟩,
    qloadPop, qloadCore⟩
  rcases Except.bind_eq_ok qloadCore with ⟨loadBurn, qloadBurn, qloadPush⟩
  have qloadDiff : Devm.DiffBurn [loadOffset]
      [Sevm.dataWord sevm loadOffset] sigPush sigLoad :=
    Devm.diffBurn_of_pop_of_pushBurn (Devm.pop_of_pop qloadPop)
      (Devm.pushBurn_of_burn_of_push (Devm.burn_of_chargeGas qloadBurn)
        (Devm.push_of_push qloadPush))
  rcases of_run_reg qshr with ⟨_, qshrCore⟩
  simp only [Rinst.run, Rinst.runCore] at qshrCore
  rcases Devm.diffBurn_of_applyBinary qshrCore with ⟨_, _, qshrDiff⟩
  exact (dispatchFrame_of_burnBy hburn).trans
    ((dispatchFrame_of_pushBurn (of_run_pushB256 qpush4)).trans
      ((dispatchFrame_of_pushBurn (of_run_calldatasize qsize)).trans
        ((dispatchFrame_of_diffBurn qltDiff).trans
          ((dispatchFrame_of_popBurnBy hpop).trans
            ((dispatchFrame_of_pushBurn (of_run_pushB256 qpush0)).trans
              ((dispatchFrame_of_diffBurn qloadDiff).trans
                ((dispatchFrame_of_pushBurn (of_run_pushB256 qpush224)).trans
                  (dispatchFrame_of_diffBurn qshrDiff))))))))

/-- A successful exact runtime walk must pass the leading short-calldata
guard.  This derives the guard word from the walk itself, so it also covers
mathematically oversized calldata whose natural length would wrap as a
`B256`. -/
theorem runtime_guard_zero_of_prog_run_ok
    {dp : DeployParams} {sevm : Sevm} {entry post : Devm}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) (.ok post)) :
    B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0 := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm mid
    ([Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] +++
      (Func.rev <?> (fsig +++ linearDispatchWith fallbackSlot (funcs dp))))
      (.ok post) at hmain
  obtain ⟨afterGuard, guardRun, branchRun⟩ :=
    runCompiledTo_prepend_inv hmain
  rcases Line.of_run_cons guardRun with ⟨afterPush, pushRun, guardRun⟩
  rcases Line.of_run_cons guardRun with ⟨afterSize, sizeRun, guardRun⟩
  rcases Line.of_run_cons guardRun with ⟨_afterLt, ltRun, nilRun⟩
  cases nilRun
  have pMid : ([] : Stack) <<+ mid.stack := nil_pref
  have pPush := prefix_of_push (of_run_pushB256 pushRun) pMid
  have pSize := prefix_of_push (of_run_calldatasize sizeRun) pPush
  have pGuard := prefix_of_lt ltRun pSize
  obtain ⟨_dispatchPre, guardZero, _pop, _dispatchRun, _tail⟩ :=
    Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok_of_prefix
      (fun revRun => by
        rcases runCompiledTo_rev_inv revRun with ⟨_rawPost, impossible, _output⟩
        cases impossible)
      pGuard branchRun
  exact guardZero

/-- An exact program run from an empty operand stack reaches the selected
runtime body with that stack restored, while every entry-frame field except
gas and stack is preserved from the actual `Prog.RunCompiledTo` prestate. -/
theorem dispatcher_body_of_prog_run_empty_frame
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector : B256} {body : Func}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selector)
    (hmember : (selector, body) ∈ funcs dp) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre body out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm mid
    ([Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] +++
      (Func.rev <?> (fsig +++ linearDispatchWith fallbackSlot (funcs dp)))) out
    at hmain
  obtain ⟨afterGuard, hguardRun, hbranch⟩ :=
    runCompiledTo_prepend_inv hmain
  rcases Line.of_run_cons hguardRun with ⟨afterPush, hpush, hrest⟩
  rcases Line.of_run_cons hrest with ⟨afterSize, hsize, hrest⟩
  rcases Line.of_run_cons hrest with ⟨_afterLt, hlt, hnil⟩
  cases hnil
  have hmidStack : mid.stack = [] := by
    rw [← hburn.stack]
    exact hentryStack
  have hpushStack : afterPush.stack = (4 : B256) :: [] :=
    stack_of_pushBurn (of_run_pushB256 hpush) hmidStack
  have hsizeStack : afterSize.stack =
      sevm.data.length.toB256 :: (4 : B256) :: [] :=
    stack_of_pushBurn (of_run_calldatasize hsize) hpushStack
  have hltDiff : ∃ x y, Stack.Diff [x, y] [B256.ltCheck x y]
      afterSize.stack afterGuard.stack := by
    rcases of_run_reg hlt with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hdiff⟩
    exact ⟨x, y, hdiff.stack⟩
  have hguardStack : afterGuard.stack = (0 : B256) :: [] := by
    have hs := stack_of_diffBurn_two hltDiff hsizeStack
    simpa [hguard] using hs
  obtain ⟨dispatchEntry, hpop, hzero⟩ : ∃ dispatchEntry,
      Devm.PopBurnBy [0] (gVerylow + gHigh) afterGuard dispatchEntry ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        dispatchEntry (fsig +++ linearDispatchWith fallbackSlot (funcs dp))
        out := by
    rcases runCompiledTo_branch_inv hbranch with hleft | hright
    · rcases hleft with ⟨armPre, hstack, hpop, harm⟩
      exact ⟨armPre, hpop, harm⟩
    · rcases hright with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hbad : (0 : B256) = w :=
        (List.cons.inj (hguardStack.symm.trans hstack)).1
      exact False.elim (hw hbad.symm)
  have hdispatchEntryStack : dispatchEntry.stack = [] :=
    stack_of_popBurnBy hpop hguardStack
  obtain ⟨afterSig, hsig, hdispatch⟩ := runCompiledTo_prepend_inv hzero
  have hsigFrame := hsig
  unfold fsig cdl shiftRight at hsig
  rcases Line.of_run_cons hsig with ⟨sigPush, qpush0, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigLoad, qload, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigShift, qpush224, hsig⟩
  rcases Line.of_run_cons hsig with ⟨_sigDone, qshr, hsigNil⟩
  cases hsigNil
  have hsigPushStack : sigPush.stack = (0 : B256) :: [] :=
    stack_of_pushBurn (of_run_pushB256 qpush0) hdispatchEntryStack
  have hloadDiff : ∃ x, Stack.Diff [x] [Sevm.dataWord sevm x]
      sigPush.stack sigLoad.stack := of_run_calldataload_val qload
  have hsigLoadStack : sigLoad.stack = Sevm.dataWord sevm 0 :: [] :=
    stack_of_diffBurn_one hloadDiff hsigPushStack
  have hsigShiftStack : sigShift.stack =
      (224 : B256) :: Sevm.dataWord sevm 0 :: [] :=
    stack_of_pushBurn (of_run_pushB256 qpush224) hsigLoadStack
  have hshrDiff : ∃ x y, Stack.Diff [x, y]
      [y >>> x.toNat] sigShift.stack afterSig.stack := by
    rcases of_run_reg qshr with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hdiff⟩
    exact ⟨x, y, hdiff.stack⟩
  have hafterSigStack : afterSig.stack = selector :: [] := by
    have hs := stack_of_diffBurn_two hshrDiff hsigShiftStack
    rw [← hselector]
    exact hs
  have hwitness := dispatchBodyWitness_of_runCompiledTo
    (funcs_selector_unique dp) hmember
    hafterSigStack hdispatch
  rcases hwitness with ⟨bodyPre, -, hbody, hbodyStack, hbodyFrame⟩
  have hprefixFrame : Devm.DispatchFramePreserved entry afterSig :=
    runtimePrefix_dispatchFrame hburn hguardRun hpop hsigFrame
  exact ⟨bodyPre, hbody, hbodyStack, hprefixFrame.trans hbodyFrame⟩

end LidoTriggerableWithdrawalsGateway
end Blanc
