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
  stor.get (roleMembershipSlot role account) ≠ 0

/-- The concrete TWG selector table has no duplicate selectors. -/
theorem funcs_selector_unique (dp : DeployParams) : selectorUnique (funcs dp) := by
  simp [selectorUnique, funcs, selPauseFor, selIsPaused, selTriggerFullWithdrawals, selPauseRole, selResumeRole, selAddFullWithdrawalRequestRole, selTwExitLimitManagerRole, selTwrLimitPosition, selVersion, selResume, selPauseUntil, selSetExitRequestLimit, selGetExitRequestLimitFullInfo, selPauseInfinitely, selGetResumeSinceTimestamp, selDefaultAdminRole, selSupportsInterface, selHasRole, selGetRoleAdmin, selGrantRole, selRevokeRole, selRenounceRole, selGetRoleMember, selGetRoleMemberCount]
  repeat' apply And.intro
  all_goals decide +kernel

/-- The optimized shared-nonpayable table also retains unique selectors. -/
theorem sharedNonpayableFuncs_selector_unique :
    selectorUnique sharedNonpayableFuncs := by
  simp [selectorUnique, sharedNonpayableFuncs, selPauseFor, selIsPaused,
    selHasRole, selGetRoleMember, selGetRoleMemberCount, selSupportsInterface,
    selResume, selDefaultAdminRole, selPauseInfinitely,
    selGetResumeSinceTimestamp, selRenounceRole, selPauseRole, selResumeRole,
    selAddFullWithdrawalRequestRole, selTwExitLimitManagerRole,
    selTwrLimitPosition, selVersion, selPauseUntil, selSetExitRequestLimit,
    selGetExitRequestLimitFullInfo, selGetRoleAdmin, selGrantRole,
    selRevokeRole]
  repeat' apply And.intro
  all_goals decide +kernel

theorem callerHasRole_collision_refusal {stor : Stor} {role account : B256}
    (habsent : stor.get (roleMembershipSlot role account) = 0) :
    ¬ CallerHasRole stor role account := by
  intro h
  exact h habsent

theorem callerHasRole_exact_lookup {stor : Stor} {role account : B256}
    (hmembership : stor.get (roleMembershipSlot role account) ≠ 0) :
    CallerHasRole stor role account := by
  exact hmembership

/-! ## Exact nested-keccak key walks

These proof seams expose the mathematical mapping key computed by the two
concrete scratch-memory variants.  They are deliberately internal route facts:
public endpoint statements continue to speak only about `CallerHasRole`. -/

private lemma prefix_of_viewRoleDataSlot
    {sevm : Sevm} {pre post : Devm} {tail : Stack} {role : B256}
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre
      (viewRoleDataSlotFrom [Ninst.pushB256 role]) post) :
    roleDataSlot role :: tail <<+ post.stack := by
  simp only [viewRoleDataSlotFrom, viewKeccakPairLines] at run
  rcases Line.of_run_cons run with ⟨s1, qrole, run⟩
  have rrole := of_run_pushB256 qrole
  have p1 := prefix_of_push rrole hp
  rcases of_run_append (mstoreAt 0) run with ⟨s2, qstore0, run⟩
  rcases of_run_mstoreAt_val qstore0 p1 with ⟨p2, hm2⟩
  rcases Line.of_run_cons run with ⟨s3, qbase, run⟩
  have rbase := of_run_pushB256 qbase
  have p3 := prefix_of_push rbase p2
  rcases of_run_append (mstoreAt 1) run with ⟨s4, qstore1, run⟩
  rcases of_run_mstoreAt_val qstore1 p3 with ⟨p4, hm4⟩
  rcases Line.of_run_cons run with ⟨s5, qsize, run⟩
  have rsize := of_run_pushB256 qsize
  have p5 := prefix_of_push rsize p4
  rcases Line.of_run_cons run with ⟨s6, qstart, run⟩
  have rstart := of_run_pushB256 qstart
  have p6 := prefix_of_push rstart p5
  rcases Line.of_run_cons run with ⟨_, qkeccak, hnil⟩
  cases hnil
  have hread : (s6.memory.read 0 64).1 =
      role.toBytes ++ accessControlRolesPosition.toBytes := by
    rw [← rstart.memory, ← rsize.memory, hm4, ← rbase.memory, hm2,
      ← rrole.memory]
    exact Mem.read_two_word_writes_at_raw pre.memory 0 role
      accessControlRolesPosition
  rcases prefix_of_keccak256_val qkeccak p6 with ⟨p7, _⟩
  change (s6.memory.read 0 64).1.keccak :: tail <<+ post.stack at p7
  rw [hread] at p7
  simpa [roleDataSlot] using p7

theorem prefix_of_viewRoleMembershipSlotForCaller
    {sevm : Sevm} {pre post : Devm} {tail : Stack} {role : B256}
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre
      (viewRoleMembershipSlotFrom [Ninst.pushB256 role] [Ninst.caller]) post) :
    roleMembershipSlot role sevm.caller.toB256 :: tail <<+ post.stack := by
  simp only [viewRoleMembershipSlotFrom, viewKeccakPairLinesRightFirst] at run
  rcases of_run_append (viewRoleDataSlotFrom [Ninst.pushB256 role]) run with
    ⟨s1, qdata, run⟩
  have p1 := prefix_of_viewRoleDataSlot hp qdata
  rcases of_run_append (mstoreAt 1) run with ⟨s2, qstore1, run⟩
  rcases of_run_mstoreAt_val qstore1 p1 with ⟨p2, hm2⟩
  rcases Line.of_run_cons run with ⟨s3, qcaller, run⟩
  have rcaller := of_run_caller qcaller
  have p3 := prefix_of_push rcaller p2
  rcases of_run_append (mstoreAt 0) run with ⟨s4, qstore0, run⟩
  rcases of_run_mstoreAt_val qstore0 p3 with ⟨p4, hm4⟩
  rcases Line.of_run_cons run with ⟨s5, qsize, run⟩
  have rsize := of_run_pushB256 qsize
  have p5 := prefix_of_push rsize p4
  rcases Line.of_run_cons run with ⟨s6, qstart, run⟩
  have rstart := of_run_pushB256 qstart
  have p6 := prefix_of_push rstart p5
  rcases Line.of_run_cons run with ⟨_, qkeccak, hnil⟩
  cases hnil
  have hread : (s6.memory.read 0 64).1 =
      sevm.caller.toB256.toBytes ++ (roleDataSlot role).toBytes := by
    rw [← rstart.memory, ← rsize.memory, hm4, ← rcaller.memory, hm2]
    exact Mem.read_two_word_writes_at_raw_right_first s1.memory 0
      sevm.caller.toB256 (roleDataSlot role)
  rcases prefix_of_keccak256_val qkeccak p6 with ⟨p7, _⟩
  change (s6.memory.read 0 64).1.keccak :: tail <<+ post.stack at p7
  rw [hread] at p7
  simpa [roleMembershipSlot] using p7

private lemma prefix_of_roleDataSlot
    {sevm : Sevm} {pre post : Devm} {tail : Stack} {role : B256}
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre (roleDataSlotFrom [Ninst.pushB256 role]) post) :
    roleDataSlot role :: tail <<+ post.stack := by
  simp only [roleDataSlotFrom, keccakPairLines] at run
  rcases Line.of_run_cons run with ⟨s1, qrole, run⟩
  have rrole := of_run_pushB256 qrole
  have p1 := prefix_of_push rrole hp
  rcases of_run_append (mstoreAt storageKeyScratchWord) run with
    ⟨s2, qstore0, run⟩
  rcases of_run_mstoreAt_val qstore0 p1 with ⟨p2, hm2raw⟩
  have hm2 : s2.memory = s1.memory.write
      (storageKeyScratchWord * 32).toNat role.toBytes := hm2raw
  rcases Line.of_run_cons run with ⟨s3, qbase, run⟩
  have rbase := of_run_pushB256 qbase
  have p3 := prefix_of_push rbase p2
  rcases of_run_append (mstoreAt storageKeyScratchNextWord) run with
    ⟨s4, qstore1, run⟩
  rcases of_run_mstoreAt_val qstore1 p3 with ⟨p4, hm4raw⟩
  have hm4 : s4.memory = s3.memory.write
      (storageKeyScratchNextWord * 32).toNat
        accessControlRolesPosition.toBytes := hm4raw
  rcases Line.of_run_cons run with ⟨s5, qsize, run⟩
  have rsize := of_run_pushB256 qsize
  have p5 := prefix_of_push rsize p4
  rcases Line.of_run_cons run with ⟨s6, qstart, run⟩
  have rstart := of_run_pushB256 qstart
  have p6raw := prefix_of_push rstart p5
  have p6 : (storageKeyScratchWord * 32) :: 64 :: tail <<+
      s6.stack := p6raw
  rcases Line.of_run_cons run with ⟨_, qkeccak, hnil⟩
  cases hnil
  have hread : (s6.memory.read (storageKeyScratchWord * 32).toNat 64).1 =
      role.toBytes ++ accessControlRolesPosition.toBytes := by
    rw [← rstart.memory, ← rsize.memory, hm4, ← rbase.memory, hm2,
      ← rrole.memory]
    exact Mem.read_two_word_writes_at_raw pre.memory
      (storageKeyScratchWord * 32).toNat role
      accessControlRolesPosition
  rcases prefix_of_keccak256_val qkeccak p6 with ⟨p7, _⟩
  change (s6.memory.read (storageKeyScratchWord * 32).toNat 64).1.keccak ::
    tail <<+ post.stack at p7
  rw [hread] at p7
  simpa [roleDataSlot] using p7

theorem prefix_of_roleMembershipSlotForCaller
    {sevm : Sevm} {pre post : Devm} {tail : Stack} {role : B256}
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre
      (roleMembershipSlotFrom [Ninst.pushB256 role] [Ninst.caller]) post) :
    roleMembershipSlot role sevm.caller.toB256 :: tail <<+ post.stack := by
  simp only [roleMembershipSlotFrom, keccakPairLinesRightFirst] at run
  rcases of_run_append (roleDataSlotFrom [Ninst.pushB256 role]) run with
    ⟨s1, qdata, run⟩
  have p1 := prefix_of_roleDataSlot hp qdata
  rcases of_run_append (mstoreAt storageKeyScratchNextWord) run with
    ⟨s2, qstore1, run⟩
  rcases of_run_mstoreAt_val qstore1 p1 with ⟨p2, hm2raw⟩
  have hm2 : s2.memory = s1.memory.write
      (storageKeyScratchNextWord * 32).toNat
        (roleDataSlot role).toBytes := hm2raw
  rcases Line.of_run_cons run with ⟨s3, qcaller, run⟩
  have rcaller := of_run_caller qcaller
  have p3 := prefix_of_push rcaller p2
  rcases of_run_append (mstoreAt storageKeyScratchWord) run with
    ⟨s4, qstore0, run⟩
  rcases of_run_mstoreAt_val qstore0 p3 with ⟨p4, hm4raw⟩
  have hm4 : s4.memory = s3.memory.write
      (storageKeyScratchWord * 32).toNat sevm.caller.toB256.toBytes := hm4raw
  rcases Line.of_run_cons run with ⟨s5, qsize, run⟩
  have rsize := of_run_pushB256 qsize
  have p5 := prefix_of_push rsize p4
  rcases Line.of_run_cons run with ⟨s6, qstart, run⟩
  have rstart := of_run_pushB256 qstart
  have p6raw := prefix_of_push rstart p5
  have p6 : (storageKeyScratchWord * 32) :: 64 :: tail <<+
      s6.stack := p6raw
  rcases Line.of_run_cons run with ⟨_, qkeccak, hnil⟩
  cases hnil
  have hread : (s6.memory.read (storageKeyScratchWord * 32).toNat 64).1 =
      sevm.caller.toB256.toBytes ++ (roleDataSlot role).toBytes := by
    rw [← rstart.memory, ← rsize.memory, hm4, ← rcaller.memory, hm2]
    exact Mem.read_two_word_writes_at_raw_right_first s1.memory
      (storageKeyScratchWord * 32).toNat sevm.caller.toB256
      (roleDataSlot role)
  rcases prefix_of_keccak256_val qkeccak p6 with ⟨p7, _⟩
  change (s6.memory.read (storageKeyScratchWord * 32).toNat 64).1.keccak ::
    tail <<+ post.stack at p7
  rw [hread] at p7
  simpa [roleMembershipSlot] using p7

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

/-! The optimized runtime selects the payable trigger before a single shared
nonpayable guard and the remaining selector table.  The route lemmas below
follow that exact compiled shape; `funcs` remains only the public ABI census. -/

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
      (Func.revert <?>
        (fsig +++ Ninst.dup 0 ::: Ninst.pushB256 selTriggerFullWithdrawals :::
          Ninst.eq :::
          ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
            (Ninst.callvalue ::: Ninst.iszero :::
              (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                Func.revert))))))
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
      (fun revertRun => by
        rcases runCompiledTo_revert_inv revertRun with ⟨_rawPost, impossible, _output⟩
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
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selector)
    (hnotTrigger : selector ≠ selTriggerFullWithdrawals)
    (hmember : (selector, body) ∈ sharedNonpayableFuncs) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre body out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm mid
    ([Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] +++
      (Func.revert <?>
        (fsig +++ Ninst.dup 0 ::: Ninst.pushB256 selTriggerFullWithdrawals :::
          Ninst.eq :::
          ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
            (Ninst.callvalue ::: Ninst.iszero :::
              (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                Func.revert)))))) out
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
        dispatchEntry
        (fsig +++ Ninst.dup 0 :::
          Ninst.pushB256 selTriggerFullWithdrawals ::: Ninst.eq :::
          ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
            (Ninst.callvalue ::: Ninst.iszero :::
              (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                Func.revert)))) out := by
    rcases runCompiledTo_branch_inv hbranch with hleft | hright
    · rcases hleft with ⟨armPre, hstack, hpop, harm⟩
      exact ⟨armPre, hpop, harm⟩
    · rcases hright with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hbad : (0 : B256) = w :=
        (List.cons.inj (hguardStack.symm.trans hstack)).1
      exact False.elim (hw hbad.symm)
  have hdispatchEntryStack : dispatchEntry.stack = [] :=
    stack_of_popBurnBy hpop hguardStack
  obtain ⟨afterSig, hsig, hroute⟩ := runCompiledTo_prepend_inv hzero
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

  obtain ⟨afterDup, hdupCompiled, hroute⟩ :=
    runCompiledTo_next_inv hroute
  obtain ⟨afterTriggerPush, htriggerPushCompiled, hroute⟩ :=
    runCompiledTo_next_inv hroute
  obtain ⟨afterTriggerEq, htriggerEqCompiled, htriggerBranch⟩ :=
    runCompiledTo_next_inv hroute
  have hdup := Ninst.Run.of_runCompiled hdupCompiled
  have htriggerPush := Ninst.Run.of_runCompiled htriggerPushCompiled
  have htriggerEq := Ninst.Run.of_runCompiled htriggerEqCompiled
  rcases of_run_dup hdup with ⟨dupWord, hdupWord, hdupPush⟩
  have hdupWordEq : dupWord = selector := by
    simpa [hafterSigStack] using hdupWord.symm
  subst dupWord
  have hdupStack : afterDup.stack = selector :: selector :: [] :=
    stack_of_pushBurn hdupPush hafterSigStack
  have htriggerPushStack : afterTriggerPush.stack =
      selTriggerFullWithdrawals :: selector :: selector :: [] :=
    stack_of_pushBurn (of_run_pushB256 htriggerPush) hdupStack
  have htriggerEqDiff : ∃ x y, Stack.Diff [x, y] [B256.eqCheck x y]
      afterTriggerPush.stack afterTriggerEq.stack := by
    rcases of_run_reg htriggerEq with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hdiff⟩
    exact ⟨x, y, hdiff.stack⟩
  have htriggerEqStack : afterTriggerEq.stack = (0 : B256) :: selector :: [] := by
    have hs := stack_of_diffBurn_two htriggerEqDiff htriggerPushStack
    simpa [B256.eqCheck, hnotTrigger, Ne.symm hnotTrigger] using hs
  obtain ⟨nonTriggerPre, htriggerPop, hnonTrigger⟩ : ∃ nonTriggerPre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) afterTriggerEq nonTriggerPre ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        nonTriggerPre
        (Ninst.callvalue ::: Ninst.iszero :::
          (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
            Func.revert)) out := by
    rcases runCompiledTo_branch_inv htriggerBranch with hzero | hsucc
    · rcases hzero with ⟨armPre, hstack, hpop, harm⟩
      exact ⟨armPre, hpop, harm⟩
    · rcases hsucc with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hbad : (0 : B256) = w :=
        (List.cons.inj (htriggerEqStack.symm.trans hstack)).1
      exact False.elim (hw hbad.symm)
  have hnonTriggerStack : nonTriggerPre.stack = selector :: [] :=
    stack_of_popBurnBy htriggerPop htriggerEqStack
  obtain ⟨afterValue, hvalueRun, hnonTrigger⟩ :=
    runCompiledTo_next_inv hnonTrigger
  obtain ⟨afterValueZero, hvalueZeroRun, hvalueBranch⟩ :=
    runCompiledTo_next_inv hnonTrigger
  have hafterValueStack : afterValue.stack =
      sevm.value :: selector :: [] :=
    stack_of_pushBurn (of_run_callvalue (Ninst.Run.of_runCompiled hvalueRun))
      hnonTriggerStack
  have hvalueZeroDiff : ∃ x, Stack.Diff [x] [x =? 0]
      afterValue.stack afterValueZero.stack := by
    rcases of_run_reg (Ninst.Run.of_runCompiled hvalueZeroRun) with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyUnary hr with ⟨x, hdiff⟩
    exact ⟨x, hdiff.stack⟩
  have hvalueZeroStack : afterValueZero.stack =
      (1 : B256) :: selector :: [] := by
    have hs := stack_of_diffBurn_one hvalueZeroDiff hafterValueStack
    simpa [hvalue, B256.eqCheck] using hs
  obtain ⟨dispatchEntry, hvaluePop, hdispatch⟩ : ∃ dispatchEntry,
      Devm.PopBurnBy [1] (gVerylow + gHigh + gJumpdest)
        afterValueZero dispatchEntry ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        dispatchEntry (linearDispatchWith fallbackSlot sharedNonpayableFuncs)
        out := by
    rcases runCompiledTo_branch_inv hvalueBranch with hzero | hsucc
    · rcases hzero with ⟨armPre, hstack, hpop, harm⟩
      have hbad : (1 : B256) = 0 :=
        (List.cons.inj (hvalueZeroStack.symm.trans hstack)).1
      exact False.elim ((by decide : (1 : B256) ≠ 0) hbad)
    · rcases hsucc with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hwEq : w = 1 :=
        (List.cons.inj (hvalueZeroStack.symm.trans hstack)).1.symm
      subst w
      exact ⟨armPre, hpop, harm⟩
  have hdispatchStack : dispatchEntry.stack = selector :: [] :=
    stack_of_popBurnBy hvaluePop hvalueZeroStack
  have hwitness := dispatchBodyWitness_of_runCompiledTo
    (by
      simp [selectorUnique, sharedNonpayableFuncs, selPauseFor, selIsPaused,
        selSupportsInterface, selResume, selDefaultAdminRole,
        selPauseInfinitely, selGetResumeSinceTimestamp, selRenounceRole,
        selHasRole, selGetRoleMember, selGetRoleMemberCount, selPauseRole,
        selResumeRole, selAddFullWithdrawalRequestRole,
        selTwExitLimitManagerRole, selTwrLimitPosition, selVersion,
        selPauseUntil, selSetExitRequestLimit,
        selGetExitRequestLimitFullInfo, selGetRoleAdmin, selGrantRole,
        selRevokeRole]
      repeat' apply And.intro
      all_goals decide +kernel)
    hmember hdispatchStack hdispatch
  rcases hwitness with ⟨bodyPre, -, hbody, hbodyStack, hbodyFrame⟩
  have hprefixFrame : Devm.DispatchFramePreserved entry afterSig :=
    runtimePrefix_dispatchFrame hburn hguardRun hpop hsigFrame
  have htriggerEqFrame : Devm.DispatchFramePreserved
      afterTriggerPush afterTriggerEq := by
    rcases of_run_reg htriggerEq with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyBinary hr with ⟨_, _, hdiff⟩
    exact dispatchFrame_of_diffBurn hdiff
  have hvalueZeroFrame : Devm.DispatchFramePreserved afterValue afterValueZero := by
    rcases of_run_reg (Ninst.Run.of_runCompiled hvalueZeroRun) with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyUnary hr with ⟨_, hdiff⟩
    exact dispatchFrame_of_diffBurn hdiff
  have hrouteFrame : Devm.DispatchFramePreserved afterSig dispatchEntry :=
    (dispatchFrame_of_pushBurn hdupPush).trans
      ((dispatchFrame_of_pushBurn (of_run_pushB256 htriggerPush)).trans
        (htriggerEqFrame.trans
          ((dispatchFrame_of_popBurnBy htriggerPop).trans
            ((dispatchFrame_of_pushBurn
                (of_run_callvalue (Ninst.Run.of_runCompiled hvalueRun))).trans
              (hvalueZeroFrame.trans
                (dispatchFrame_of_popBurnBy hvaluePop))))))
  exact ⟨bodyPre, hbody, hbodyStack,
    hprefixFrame.trans (hrouteFrame.trans hbodyFrame)⟩

/-- A successful non-trigger entry must pass the one shared nonpayable guard.
This is intentionally proved from the optimized runtime prefix itself; the
public success theorems therefore retain their conclusion that message value
was zero even though `nonpayable` is no longer duplicated in every table arm. -/
theorem runtime_value_zero_of_prog_run_ok_of_nontrigger
    {dp : DeployParams} {sevm : Sevm} {entry post : Devm}
    {selector : B256}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) (.ok post))
    (hentryStack : entry.stack = [])
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selector)
    (hnotTrigger : selector ≠ selTriggerFullWithdrawals) :
    sevm.value = 0 := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm mid
    ([Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] +++
      (Func.revert <?>
        (fsig +++ Ninst.dup 0 ::: Ninst.pushB256 selTriggerFullWithdrawals :::
          Ninst.eq :::
          ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
            (Ninst.callvalue ::: Ninst.iszero :::
              (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                Func.revert)))))) (.ok post) at hmain
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
  obtain ⟨dispatchEntry, _hguardPop, hzero⟩ : ∃ dispatchEntry,
      Devm.PopBurnBy [0] (gVerylow + gHigh) afterGuard dispatchEntry ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        dispatchEntry
        (fsig +++ Ninst.dup 0 :::
          Ninst.pushB256 selTriggerFullWithdrawals ::: Ninst.eq :::
          ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
            (Ninst.callvalue ::: Ninst.iszero :::
              (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                Func.revert)))) (.ok post) := by
    rcases runCompiledTo_branch_inv hbranch with hzero | hsucc
    · rcases hzero with ⟨armPre, hstack, hpop, harm⟩
      exact ⟨armPre, hpop, harm⟩
    · rcases hsucc with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hbad : (0 : B256) = w :=
        (List.cons.inj (hguardStack.symm.trans hstack)).1
      exact False.elim (hw hbad.symm)
  obtain ⟨afterSig, hsig, hroute⟩ := runCompiledTo_prepend_inv hzero
  have pDispatch : ([] : Stack) <<+ dispatchEntry.stack := nil_pref
  have pSig : selector :: [] <<+ afterSig.stack := by
    have p := prefix_of_fsig pDispatch hsig
    simpa [hselector] using p
  obtain ⟨afterDup, hdupCompiled, hroute⟩ :=
    runCompiledTo_next_inv hroute
  obtain ⟨afterTriggerPush, htriggerPushCompiled, hroute⟩ :=
    runCompiledTo_next_inv hroute
  obtain ⟨afterTriggerEq, htriggerEqCompiled, htriggerBranch⟩ :=
    runCompiledTo_next_inv hroute
  have hdup := Ninst.Run.of_runCompiled hdupCompiled
  have htriggerPush := Ninst.Run.of_runCompiled htriggerPushCompiled
  have htriggerEq := Ninst.Run.of_runCompiled htriggerEqCompiled
  rcases of_run_dup hdup with ⟨dupWord, hdupWord, hdupPush⟩
  have hdupWordEq : dupWord = selector := by
    rcases pSig with ⟨tail, hstack⟩
    rw [hstack] at hdupWord
    simpa using hdupWord.symm
  subst dupWord
  have pDup : selector :: selector :: [] <<+ afterDup.stack :=
    prefix_of_push hdupPush pSig
  have pTriggerPush : selTriggerFullWithdrawals :: selector :: selector :: [] <<+
      afterTriggerPush.stack :=
    prefix_of_push (of_run_pushB256 htriggerPush) pDup
  have pTriggerEq : (0 : B256) :: selector :: [] <<+
      afterTriggerEq.stack := by
    have p := prefix_of_eq htriggerEq pTriggerPush
    simpa [B256.eqCheck, hnotTrigger, Ne.symm hnotTrigger] using p
  obtain ⟨nonTriggerPre, _htriggerPop, hnonTrigger, pNonTrigger⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pTriggerEq htriggerBranch
  have hwrapped : Func.RunCompiledTo
      ((runtime dp).main :: (runtime dp).aux) sevm nonTriggerPre
      (nonpayable (linearDispatchWith fallbackSlot sharedNonpayableFuncs))
      (.ok post) := by
    simpa [nonpayable] using hnonTrigger
  obtain ⟨valueZero, _bodyPre, _bodyRun, _pBody, _bodyStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_ok pNonTrigger hwrapped
  exact valueZero

/-- The payable trigger is selected before the shared nonpayable guard.  This
is the exact empty-stack route to its unwrapped executable body. -/
theorem trigger_body_of_prog_run_empty_frame
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selTriggerFullWithdrawals) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre (triggerFullWithdrawals dp) out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm mid
    ([Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] +++
      (Func.revert <?>
        (fsig +++ Ninst.dup 0 ::: Ninst.pushB256 selTriggerFullWithdrawals :::
          Ninst.eq :::
          ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
            (Ninst.callvalue ::: Ninst.iszero :::
              (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                Func.revert)))))) out at hmain
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
  obtain ⟨dispatchEntry, hguardPop, hzero⟩ : ∃ dispatchEntry,
      Devm.PopBurnBy [0] (gVerylow + gHigh) afterGuard dispatchEntry ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        dispatchEntry
        (fsig +++ Ninst.dup 0 :::
          Ninst.pushB256 selTriggerFullWithdrawals ::: Ninst.eq :::
          ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
            (Ninst.callvalue ::: Ninst.iszero :::
              (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                Func.revert)))) out := by
    rcases runCompiledTo_branch_inv hbranch with hzero | hsucc
    · rcases hzero with ⟨armPre, hstack, hpop, harm⟩
      exact ⟨armPre, hpop, harm⟩
    · rcases hsucc with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hbad : (0 : B256) = w :=
        (List.cons.inj (hguardStack.symm.trans hstack)).1
      exact False.elim (hw hbad.symm)
  have hdispatchEntryStack : dispatchEntry.stack = [] :=
    stack_of_popBurnBy hguardPop hguardStack
  obtain ⟨afterSig, hsig, hroute⟩ := runCompiledTo_prepend_inv hzero
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
  have hafterSigStack : afterSig.stack = selTriggerFullWithdrawals :: [] := by
    have hs := stack_of_diffBurn_two hshrDiff hsigShiftStack
    rw [← hselector]
    exact hs
  obtain ⟨afterDup, hdupCompiled, hroute⟩ := runCompiledTo_next_inv hroute
  obtain ⟨afterTriggerPush, htriggerPushCompiled, hroute⟩ :=
    runCompiledTo_next_inv hroute
  obtain ⟨afterTriggerEq, htriggerEqCompiled, htriggerBranch⟩ :=
    runCompiledTo_next_inv hroute
  have hdup := Ninst.Run.of_runCompiled hdupCompiled
  have htriggerPush := Ninst.Run.of_runCompiled htriggerPushCompiled
  have htriggerEq := Ninst.Run.of_runCompiled htriggerEqCompiled
  rcases of_run_dup hdup with ⟨dupWord, hdupWord, hdupPush⟩
  have hdupWordEq : dupWord = selTriggerFullWithdrawals := by
    simpa [hafterSigStack] using hdupWord.symm
  subst dupWord
  have hdupStack : afterDup.stack =
      selTriggerFullWithdrawals :: selTriggerFullWithdrawals :: [] :=
    stack_of_pushBurn hdupPush hafterSigStack
  have htriggerPushStack : afterTriggerPush.stack =
      selTriggerFullWithdrawals :: selTriggerFullWithdrawals ::
        selTriggerFullWithdrawals :: [] :=
    stack_of_pushBurn (of_run_pushB256 htriggerPush) hdupStack
  have htriggerEqDiff : ∃ x y, Stack.Diff [x, y] [B256.eqCheck x y]
      afterTriggerPush.stack afterTriggerEq.stack := by
    rcases of_run_reg htriggerEq with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hdiff⟩
    exact ⟨x, y, hdiff.stack⟩
  have htriggerEqStack : afterTriggerEq.stack =
      (1 : B256) :: selTriggerFullWithdrawals :: [] := by
    have hs := stack_of_diffBurn_two htriggerEqDiff htriggerPushStack
    simpa [B256.eqCheck] using hs
  obtain ⟨triggerPre, htriggerPop, htriggerArm⟩ : ∃ triggerPre,
      Devm.PopBurnBy [1] (gVerylow + gHigh + gJumpdest)
        afterTriggerEq triggerPre ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        triggerPre (Ninst.pop ::: triggerFullWithdrawals dp) out := by
    rcases runCompiledTo_branch_inv htriggerBranch with hzero | hsucc
    · rcases hzero with ⟨armPre, hstack, hpop, harm⟩
      have hbad : (1 : B256) = 0 :=
        (List.cons.inj (htriggerEqStack.symm.trans hstack)).1
      exact False.elim ((by decide : (1 : B256) ≠ 0) hbad)
    · rcases hsucc with ⟨w, armPre, hw, hstack, hpop, harm⟩
      have hwEq : w = 1 :=
        (List.cons.inj (htriggerEqStack.symm.trans hstack)).1.symm
      subst w
      exact ⟨armPre, hpop, harm⟩
  have htriggerPreStack : triggerPre.stack =
      selTriggerFullWithdrawals :: [] :=
    stack_of_popBurnBy htriggerPop htriggerEqStack
  obtain ⟨bodyPre, hselectorPopCompiled, hbody⟩ :=
    runCompiledTo_next_inv htriggerArm
  have hselectorPop := Ninst.Run.of_runCompiled hselectorPopCompiled
  rcases of_run_pop hselectorPop with ⟨popped, hpopBurn⟩
  have hpopStack :
      selTriggerFullWithdrawals = popped ∧ bodyPre.stack = [] := by
    simpa [Devm.PopBurn, Stack.Pop, Split, htriggerPreStack] using
      hpopBurn.stack
  have hpopped : popped = selTriggerFullWithdrawals := by
    exact hpopStack.1.symm
  subst popped
  have hbodyStack : bodyPre.stack = [] := by
    exact hpopStack.2
  have htriggerEqFrame : Devm.DispatchFramePreserved
      afterTriggerPush afterTriggerEq := by
    rcases of_run_reg htriggerEq with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyBinary hr with ⟨_, _, hdiff⟩
    exact dispatchFrame_of_diffBurn hdiff
  have hselectorPopFrame : Devm.DispatchFramePreserved triggerPre bodyPre := by
    constructor
    · trivial
    · exact hpopBurn.memory
    · trivial
    · exact hpopBurn.logs
    · exact hpopBurn.refundCounter
    · exact hpopBurn.output
    · exact hpopBurn.accountsToDelete
    · exact hpopBurn.returnData
    · exact hpopBurn.error
    · exact hpopBurn.accessedAddresses
    · exact hpopBurn.accessedStorageKeys
    · exact hpopBurn.state
    · exact hpopBurn.createdAccounts
    · exact hpopBurn.transientStorage
  have hprefixFrame : Devm.DispatchFramePreserved entry afterSig :=
    runtimePrefix_dispatchFrame hburn hguardRun hguardPop hsigFrame
  have hrouteFrame : Devm.DispatchFramePreserved afterSig bodyPre :=
    (dispatchFrame_of_pushBurn hdupPush).trans
      ((dispatchFrame_of_pushBurn (of_run_pushB256 htriggerPush)).trans
        (htriggerEqFrame.trans
          ((dispatchFrame_of_popBurnBy htriggerPop).trans hselectorPopFrame)))
  exact ⟨bodyPre, hbody, hbodyStack, hprefixFrame.trans hrouteFrame⟩

end LidoTriggerableWithdrawalsGateway
end Blanc
