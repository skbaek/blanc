import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute

/-!
# Exact TWG `onlyRole` routes

The gateway's role gate is shared by pause, resume, role mutation, and limit
management endpoints.  This family-local seam inverts its three storage reads
and all three guards once.  It classifies an arbitrary terminal outcome as
either the authorized body walk, the zero-index missing-role call, a stored-role
collision, or a stored-account collision.  Every route retains the surviving
stack tail and storage preservation across the read-only prefix.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

private theorem roleKeyWord_eq (role account : B256) (region : Nat) :
    regionWord region |||
        (low252Mask &&& ((addressMask &&& account) ^^^ role)) =
      taggedSlot region (roleLookupPayload role account) := by
  unfold taggedSlot roleLookupPayload canonicalAccount
  rw [B256.and_comm addressMask account,
    B256.xor_comm (account &&& addressMask) role,
    B256.and_comm low252Mask (role ^^^ (account &&& addressMask))]
  exact congrArg (regionWord region ||| ·)
    (B256.and_idem_right
      (role ^^^ (account &&& addressMask)) low252Mask).symm

private lemma prefix_of_roleKeyForCaller
    {e : Sevm} {s s' : Devm} {xs : Stack} (role : B256) (region : Nat)
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (roleKeyForCaller role (regionWord region)) s') :
    taggedSlot region (roleLookupPayload role e.caller.toB256) :: xs <<+
      s'.stack := by
  unfold roleKeyForCaller at run
  rcases Line.of_run_cons run with ⟨s1, qrole, run⟩
  rcases Line.of_run_cons run with ⟨s2, qcaller, run⟩
  rcases Line.of_run_cons run with ⟨s3, qmask, run⟩
  rcases Line.of_run_cons run with ⟨s4, qand1, run⟩
  rcases Line.of_run_cons run with ⟨s5, qxor, run⟩
  rcases Line.of_run_cons run with ⟨s6, qlow, run⟩
  rcases Line.of_run_cons run with ⟨s7, qand2, run⟩
  rcases Line.of_run_cons run with ⟨s8, qregion, run⟩
  rcases Line.of_run_cons run with ⟨_, qor, hnil⟩
  cases hnil
  have p1 := prefix_of_push (of_run_pushB256 qrole) hp
  have p2 := prefix_of_push (of_run_caller qcaller) p1
  have p3 := prefix_of_push (of_run_pushB256 qmask) p2
  have p4 := prefix_of_and qand1 p3
  have p5 := prefix_of_xor qxor p4
  have p6 := prefix_of_push (of_run_pushB256 qlow) p5
  have p7 := prefix_of_and qand2 p6
  have p8 := prefix_of_push (of_run_pushB256 qregion) p7
  have p9 := prefix_of_or qor p8
  simpa [roleKeyWord_eq] using p9

/-- Sufficient calldata forces the live arm of the gateway's static-argument
guard.  The result is outcome-polymorphic so authorization and success proofs
can peel the same wrapper. -/
theorem requireStaticArgs_body_of_sufficient_calldata
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {words : Nat} {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hsize : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words)) = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (requireStaticArgs words body) out) :
    ∃ bodyPre,
      Func.RunCompiledTo fs sevm bodyPre body out ∧
      tail <<+ bodyPre.stack ∧
      Devm.getStor pre = Devm.getStor bodyPre := by
  unfold requireStaticArgs at run
  change Func.RunCompiledTo fs sevm pre
    (([Ninst.pushB256 (Nat.toB256 (4 + 32 * words)), Ninst.calldatasize,
      Ninst.lt]) +++
      (Func.rev <?> body)) out at run
  obtain ⟨testPre, testLine, branchRun⟩ := runCompiledTo_prepend_inv run
  rcases Line.of_run_cons testLine with ⟨afterWord, qword, testLine⟩
  rcases Line.of_run_cons testLine with ⟨afterSize, qsize, testLine⟩
  rcases Line.of_run_cons testLine with ⟨_, qlt, hnil⟩
  cases hnil
  have p1 := prefix_of_push (of_run_pushB256 qword) hp
  have p2 := prefix_of_push (of_run_calldatasize qsize) p1
  have p3 := prefix_of_lt qlt p2
  have pZero : (0 : B256) :: tail <<+ testPre.stack := by
    simpa [hsize] using p3
  obtain ⟨bodyPre, hpop, bodyRun, pBody⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  have bodyStor : Devm.getStor pre = Devm.getStor bodyPre :=
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons qword (Line.Run.cons qsize
        (Line.Run.cons qlt Line.Run.nil)))).trans
      (funext (getStor_eq_of_state_eq hpop.state))
  exact ⟨bodyPre, bodyRun, pBody, bodyStor⟩

/-- The four exact continuations of the gateway's shared `onlyRole` modifier. -/
inductive OnlyRoleRoute
    (dp : DeployParams) (sevm : Sevm) (pre : Devm)
    (role : B256) (body : Func) (tail : Stack) (out : Execution) : Prop
  | authorized (bodyPre : Devm)
      (hasRole : CallerHasRole (Devm.getStor pre sevm.currentTarget)
        role sevm.caller.toB256)
      (bodyRun : Func.RunCompiledTo
        ((runtime dp).main :: (runtime dp).aux) sevm bodyPre body out)
      (stack : tail <<+ bodyPre.stack)
      (storage : Devm.getStor pre = Devm.getStor bodyPre)
  | missingRole (callPre : Devm)
      (indexZero : pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot role sevm.caller.toB256) = 0)
      (callRun : Func.RunCompiledTo
        ((runtime dp).main :: (runtime dp).aux) sevm callPre
          (.call missingRoleSlot) out)
      (stack : tail <<+ callPre.stack)
      (storage : Devm.getStor pre = Devm.getStor callPre)
  | roleCollision (callPre : Devm)
      (indexNonzero : pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot role sevm.caller.toB256) ≠ 0)
      (roleMismatch : pre.getStorVal sevm.currentTarget
        (roleLookupRoleSlot role sevm.caller.toB256) ≠ role)
      (callRun : Func.RunCompiledTo
        ((runtime dp).main :: (runtime dp).aux) sevm callPre
          (.call collisionRefusalSlot) out)
      (stack : tail <<+ callPre.stack)
      (storage : Devm.getStor pre = Devm.getStor callPre)
  | accountCollision (callPre : Devm)
      (indexNonzero : pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot role sevm.caller.toB256) ≠ 0)
      (roleMatch : pre.getStorVal sevm.currentTarget
        (roleLookupRoleSlot role sevm.caller.toB256) = role)
      (accountMismatch : pre.getStorVal sevm.currentTarget
        (roleLookupAccountSlot role sevm.caller.toB256) ≠
          canonicalAccount sevm.caller.toB256)
      (callRun : Func.RunCompiledTo
        ((runtime dp).main :: (runtime dp).aux) sevm callPre
          (.call collisionRefusalSlot) out)
      (stack : tail <<+ callPre.stack)
      (storage : Devm.getStor pre = Devm.getStor callPre)

/-- Exact arbitrary-outcome traversal of the shared `onlyRole` modifier. -/
theorem onlyRole_route
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {role : B256} {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (onlyRole role body) out) :
    OnlyRoleRoute dp sevm pre role body tail out := by
  unfold onlyRole at run
  obtain ⟨indexLoadPre, indexKeyRun, run⟩ := runCompiledTo_prepend_inv run
  have pIndexKey0 := prefix_of_roleKeyForCaller role
    roleLookupIndexRegion hp indexKeyRun
  have pIndexKey : roleLookupIndexSlot role sevm.caller.toB256 :: tail <<+
      indexLoadPre.stack := by
    simpa [roleLookupIndexSlot] using pIndexKey0
  obtain ⟨indexLoadPost, qindexLoad, run⟩ := runCompiledTo_next_inv run
  obtain ⟨indexTest, qindexZero, indexBranch⟩ := runCompiledTo_next_inv run
  have rindexLoad := Ninst.Run.of_runCompiled qindexLoad
  have rindexZero := Ninst.Run.of_runCompiled qindexZero
  obtain ⟨indexValue, pIndexValue, hIndexValue⟩ :=
    prefix_of_sload rindexLoad pIndexKey
  have pIndexTest := prefix_of_iszero rindexZero pIndexValue
  have indexLoadStor : Devm.getStor pre = Devm.getStor indexLoadPre :=
    Line.of_inv Devm.getStor (by line_inv) indexKeyRun
  have hIndexAtEntry : indexValue =
      pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot role sevm.caller.toB256) := by
    rw [hIndexValue]
    change (Devm.getStor indexLoadPre sevm.currentTarget).get
        (roleLookupIndexSlot role sevm.caller.toB256) =
      (Devm.getStor pre sevm.currentTarget).get
        (roleLookupIndexSlot role sevm.caller.toB256)
    rw [← congrFun indexLoadStor sevm.currentTarget]
  have indexRoute :
      (∃ roleRecordPre,
        Devm.PopBurnBy [0] (gVerylow + gHigh) indexTest roleRecordPre ∧
        Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
          roleRecordPre (roleRecordCheck role body) out ∧
        tail <<+ roleRecordPre.stack ∧ indexValue ≠ 0) ∨
      OnlyRoleRoute dp sevm pre role body tail out := by
    by_cases hne : indexValue ≠ 0
    · have pzero : (0 : B256) :: tail <<+ indexTest.stack := by
        simpa [B256.eqCheck, hne] using pIndexTest
      obtain ⟨roleRecordPre, hpop, roleRecordRun, pRoleRecord⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pzero indexBranch
      exact Or.inl ⟨roleRecordPre, hpop, roleRecordRun, pRoleRecord, hne⟩
    · have hz : indexValue = 0 := by simpa using hne
      have pone : (1 : B256) :: tail <<+ indexTest.stack := by
        simpa [hz, B256.eqCheck] using pIndexTest
      obtain ⟨callPre, _, -, hpop, missingRun, pCall⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pone indexBranch
      have callStor : Devm.getStor pre = Devm.getStor callPre :=
        indexLoadStor.trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rindexLoad).trans
            ((Ninst.Hinv.inv (f := Devm.getStor) rindexZero).trans
              (funext (getStor_eq_of_state_eq hpop.state))))
      have entryZero : pre.getStorVal sevm.currentTarget
          (roleLookupIndexSlot role sevm.caller.toB256) = 0 :=
        hIndexAtEntry.symm.trans hz
      exact Or.inr (.missingRole callPre entryZero missingRun pCall callStor)
  rcases indexRoute with hcontinue | hdone
  swap
  exact hdone
  obtain ⟨roleRecordPre, hindexPop, roleRecordRun, pRoleRecord,
    hindexNonzero⟩ := hcontinue
  have roleRecordStor : Devm.getStor pre = Devm.getStor roleRecordPre :=
    indexLoadStor.trans
      ((Ninst.Hinv.inv (f := Devm.getStor) rindexLoad).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rindexZero).trans
          (funext (getStor_eq_of_state_eq hindexPop.state))))

  unfold roleRecordCheck at roleRecordRun
  obtain ⟨roleLoadPre, roleKeyRun, roleRecordRun⟩ :=
    runCompiledTo_prepend_inv roleRecordRun
  have pRoleKey0 := prefix_of_roleKeyForCaller role
    roleLookupRoleRegion pRoleRecord roleKeyRun
  have pRoleKey : roleLookupRoleSlot role sevm.caller.toB256 :: tail <<+
      roleLoadPre.stack := by
    simpa [roleLookupRoleSlot] using pRoleKey0
  obtain ⟨roleLoadPost, qroleLoad, roleRecordRun⟩ :=
    runCompiledTo_next_inv roleRecordRun
  obtain ⟨rolePushPost, qrolePush, roleRecordRun⟩ :=
    runCompiledTo_next_inv roleRecordRun
  obtain ⟨roleTest, qroleEq, roleBranch⟩ :=
    runCompiledTo_next_inv roleRecordRun
  have rroleLoad := Ninst.Run.of_runCompiled qroleLoad
  have rrolePush := Ninst.Run.of_runCompiled qrolePush
  have rroleEq := Ninst.Run.of_runCompiled qroleEq
  obtain ⟨storedRole, pStoredRole, hStoredRole⟩ :=
    prefix_of_sload rroleLoad pRoleKey
  have pRolePush := prefix_of_push (of_run_pushB256 rrolePush) pStoredRole
  have pRoleTest := prefix_of_eq rroleEq pRolePush
  have roleLoadStor : Devm.getStor pre = Devm.getStor roleLoadPre :=
    roleRecordStor.trans (Line.of_inv Devm.getStor (by line_inv) roleKeyRun)
  have hStoredRoleAtEntry : storedRole =
      pre.getStorVal sevm.currentTarget
        (roleLookupRoleSlot role sevm.caller.toB256) := by
    rw [hStoredRole]
    change (Devm.getStor roleLoadPre sevm.currentTarget).get
        (roleLookupRoleSlot role sevm.caller.toB256) =
      (Devm.getStor pre sevm.currentTarget).get
        (roleLookupRoleSlot role sevm.caller.toB256)
    rw [← congrFun roleLoadStor sevm.currentTarget]
  have hIndexNonzeroAtEntry : pre.getStorVal sevm.currentTarget
      (roleLookupIndexSlot role sevm.caller.toB256) ≠ 0 := by
    rw [← hIndexAtEntry]
    exact hindexNonzero
  have roleRoute :
      (∃ roleAccountPre,
        Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
          roleAccountPre (roleAccountCheck role body) out ∧
        tail <<+ roleAccountPre.stack ∧ storedRole = role ∧
        Devm.getStor roleTest = Devm.getStor roleAccountPre) ∨
      OnlyRoleRoute dp sevm pre role body tail out := by
    by_cases hmatch : storedRole = role
    · have pone : (1 : B256) :: tail <<+ roleTest.stack := by
        simpa [hmatch, B256.eqCheck] using pRoleTest
      obtain ⟨roleAccountPre, _, -, hpop, roleAccountRun, pRoleAccount⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pone roleBranch
      exact Or.inl
        ⟨roleAccountPre, roleAccountRun, pRoleAccount, hmatch,
          funext (getStor_eq_of_state_eq hpop.state)⟩
    · have pzero : (0 : B256) :: tail <<+ roleTest.stack := by
        simpa [B256.eqCheck, Ne.symm hmatch] using pRoleTest
      obtain ⟨callPre, hpop, collisionRun, pCall⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pzero roleBranch
      have callStor : Devm.getStor pre = Devm.getStor callPre :=
        roleLoadStor.trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rroleLoad).trans
            ((Ninst.Hinv.inv (f := Devm.getStor) rrolePush).trans
              ((Ninst.Hinv.inv (f := Devm.getStor) rroleEq).trans
                (funext (getStor_eq_of_state_eq hpop.state)))))
      have entryMismatch : pre.getStorVal sevm.currentTarget
          (roleLookupRoleSlot role sevm.caller.toB256) ≠ role := by
        intro hentry
        exact hmatch (hStoredRoleAtEntry.trans hentry)
      exact Or.inr (.roleCollision callPre hIndexNonzeroAtEntry
        entryMismatch collisionRun pCall callStor)
  rcases roleRoute with hcontinue | hdone
  swap
  exact hdone
  obtain ⟨roleAccountPre, roleAccountRun, pRoleAccount, hroleMatch,
    rolePopStor⟩ := hcontinue
  have roleAccountStor : Devm.getStor pre = Devm.getStor roleAccountPre :=
    roleLoadStor.trans
      ((Ninst.Hinv.inv (f := Devm.getStor) rroleLoad).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rrolePush).trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rroleEq).trans
            rolePopStor)))

  unfold roleAccountCheck at roleAccountRun
  obtain ⟨accountLoadPre, accountKeyRun, roleAccountRun⟩ :=
    runCompiledTo_prepend_inv roleAccountRun
  have pAccountKey0 := prefix_of_roleKeyForCaller role
    roleLookupAccountRegion pRoleAccount accountKeyRun
  have pAccountKey : roleLookupAccountSlot role sevm.caller.toB256 :: tail <<+
      accountLoadPre.stack := by
    simpa [roleLookupAccountSlot] using pAccountKey0
  obtain ⟨accountLoadPost, qaccountLoad, roleAccountRun⟩ :=
    runCompiledTo_next_inv roleAccountRun
  obtain ⟨accountCallerPost, qaccountCaller, roleAccountRun⟩ :=
    runCompiledTo_next_inv roleAccountRun
  obtain ⟨accountMaskPost, qaccountMask, roleAccountRun⟩ :=
    runCompiledTo_next_inv roleAccountRun
  obtain ⟨accountCanonicalPost, qaccountAnd, roleAccountRun⟩ :=
    runCompiledTo_next_inv roleAccountRun
  obtain ⟨accountTest, qaccountEq, accountBranch⟩ :=
    runCompiledTo_next_inv roleAccountRun
  have raccountLoad := Ninst.Run.of_runCompiled qaccountLoad
  have raccountCaller := Ninst.Run.of_runCompiled qaccountCaller
  have raccountMask := Ninst.Run.of_runCompiled qaccountMask
  have raccountAnd := Ninst.Run.of_runCompiled qaccountAnd
  have raccountEq := Ninst.Run.of_runCompiled qaccountEq
  obtain ⟨storedAccount, pStoredAccount, hStoredAccount⟩ :=
    prefix_of_sload raccountLoad pAccountKey
  have pAccountCaller :=
    prefix_of_push (of_run_caller raccountCaller) pStoredAccount
  have pAccountMask :=
    prefix_of_push (of_run_pushB256 raccountMask) pAccountCaller
  have pCanonical0 := prefix_of_and raccountAnd pAccountMask
  have pCanonical : canonicalAccount sevm.caller.toB256 :: storedAccount ::
      tail <<+ accountCanonicalPost.stack := by
    rw [B256.and_comm addressMask sevm.caller.toB256] at pCanonical0
    change canonicalAccount sevm.caller.toB256 :: storedAccount :: tail <<+
      accountCanonicalPost.stack at pCanonical0
    exact pCanonical0
  have pAccountTest := prefix_of_eq raccountEq pCanonical
  have accountLoadStor : Devm.getStor pre = Devm.getStor accountLoadPre :=
    roleAccountStor.trans
      (Line.of_inv Devm.getStor (by line_inv) accountKeyRun)
  have hStoredAccountAtEntry : storedAccount =
      pre.getStorVal sevm.currentTarget
        (roleLookupAccountSlot role sevm.caller.toB256) := by
    rw [hStoredAccount]
    change (Devm.getStor accountLoadPre sevm.currentTarget).get
        (roleLookupAccountSlot role sevm.caller.toB256) =
      (Devm.getStor pre sevm.currentTarget).get
        (roleLookupAccountSlot role sevm.caller.toB256)
    rw [← congrFun accountLoadStor sevm.currentTarget]
  have hRoleMatchAtEntry : pre.getStorVal sevm.currentTarget
      (roleLookupRoleSlot role sevm.caller.toB256) = role :=
    hStoredRoleAtEntry.symm.trans hroleMatch
  have accountRoute :
      (∃ bodyPre,
        Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
          bodyPre body out ∧
        tail <<+ bodyPre.stack ∧
        storedAccount = canonicalAccount sevm.caller.toB256 ∧
        Devm.getStor accountTest = Devm.getStor bodyPre) ∨
      OnlyRoleRoute dp sevm pre role body tail out := by
    by_cases hmatch :
        storedAccount = canonicalAccount sevm.caller.toB256
    · have pone : (1 : B256) :: tail <<+ accountTest.stack := by
        simpa [hmatch, B256.eqCheck] using pAccountTest
      obtain ⟨bodyPre, _, -, hpop, bodyRun, pBody⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pone accountBranch
      exact Or.inl ⟨bodyPre, bodyRun, pBody, hmatch,
        funext (getStor_eq_of_state_eq hpop.state)⟩
    · have pzero : (0 : B256) :: tail <<+ accountTest.stack := by
        simpa [B256.eqCheck, Ne.symm hmatch] using pAccountTest
      obtain ⟨callPre, hpop, collisionRun, pCall⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pzero accountBranch
      have callStor : Devm.getStor pre = Devm.getStor callPre := by
        calc
          Devm.getStor pre = Devm.getStor accountLoadPre := accountLoadStor
          _ = Devm.getStor accountLoadPost :=
            Ninst.Hinv.inv (f := Devm.getStor) raccountLoad
          _ = Devm.getStor accountCallerPost :=
            Ninst.Hinv.inv (f := Devm.getStor) raccountCaller
          _ = Devm.getStor accountMaskPost :=
            Ninst.Hinv.inv (f := Devm.getStor) raccountMask
          _ = Devm.getStor accountCanonicalPost :=
            Ninst.Hinv.inv (f := Devm.getStor) raccountAnd
          _ = Devm.getStor accountTest :=
            Ninst.Hinv.inv (f := Devm.getStor) raccountEq
          _ = Devm.getStor callPre :=
            funext (getStor_eq_of_state_eq hpop.state)
      have entryMismatch : pre.getStorVal sevm.currentTarget
          (roleLookupAccountSlot role sevm.caller.toB256) ≠
            canonicalAccount sevm.caller.toB256 := by
        intro hentry
        exact hmatch (hStoredAccountAtEntry.trans hentry)
      exact Or.inr (.accountCollision callPre hIndexNonzeroAtEntry
        hRoleMatchAtEntry entryMismatch collisionRun pCall callStor)
  rcases accountRoute with hcontinue | hdone
  swap
  exact hdone
  obtain ⟨bodyPre, bodyRun, pBody, haccountMatch, accountPopStor⟩ :=
    hcontinue
  have bodyStor : Devm.getStor pre = Devm.getStor bodyPre := by
    calc
      Devm.getStor pre = Devm.getStor accountLoadPre := accountLoadStor
      _ = Devm.getStor accountLoadPost :=
        Ninst.Hinv.inv (f := Devm.getStor) raccountLoad
      _ = Devm.getStor accountCallerPost :=
        Ninst.Hinv.inv (f := Devm.getStor) raccountCaller
      _ = Devm.getStor accountMaskPost :=
        Ninst.Hinv.inv (f := Devm.getStor) raccountMask
      _ = Devm.getStor accountCanonicalPost :=
        Ninst.Hinv.inv (f := Devm.getStor) raccountAnd
      _ = Devm.getStor accountTest :=
        Ninst.Hinv.inv (f := Devm.getStor) raccountEq
      _ = Devm.getStor bodyPre := accountPopStor
  have authorized : CallerHasRole (Devm.getStor pre sevm.currentTarget)
      role sevm.caller.toB256 := by
    apply callerHasRole_exact_lookup
    · change pre.getStorVal sevm.currentTarget
        (roleLookupRoleSlot role sevm.caller.toB256) = role
      exact hStoredRoleAtEntry.symm.trans hroleMatch
    · change pre.getStorVal sevm.currentTarget
        (roleLookupAccountSlot role sevm.caller.toB256) =
          canonicalAccount sevm.caller.toB256
      exact hStoredAccountAtEntry.symm.trans haccountMatch
    · change pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot role sevm.caller.toB256) ≠ 0
      rw [← hIndexAtEntry]
      exact hindexNonzero
  exact .authorized bodyPre authorized bodyRun pBody bodyStor

/-- A successful `onlyRole` traversal reaches the protected body and proves
the exact role record at the modifier entry. -/
theorem onlyRole_body_of_ok
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    {role : B256} {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (onlyRole role body) (.ok post)) :
    ∃ bodyPre,
      CallerHasRole (Devm.getStor pre sevm.currentTarget)
          role sevm.caller.toB256 ∧
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre body (.ok post) ∧
      tail <<+ bodyPre.stack ∧
      Devm.getStor pre = Devm.getStor bodyPre := by
  cases onlyRole_route hp run with
  | authorized bodyPre hasRole bodyRun stack storage =>
    exact ⟨bodyPre, hasRole, bodyRun, stack, storage⟩
  | missingRole callPre indexZero callRun stack storage =>
    have hget : ((runtime dp).main :: (runtime dp).aux)[missingRoleSlot]? =
        some (runtimeError "AccessControlUnauthorizedAccount" []) := by
      simp [runtime, aux, baseAux, missingRoleSlot]
    exact (Func.RunCompiledTo.not_ok_call_revSelector
      (by simpa [runtimeError] using hget) callRun).elim
  | roleCollision callPre indexNonzero roleMismatch callRun stack storage =>
    have hget : ((runtime dp).main :: (runtime dp).aux)[collisionRefusalSlot]? =
        some Func.rev := by
      simp [runtime, aux, baseAux, collisionRefusalSlot]
    exact (Func.RunCompiledTo.not_ok_call_rev hget callRun).elim
  | accountCollision callPre indexNonzero roleMatch accountMismatch callRun
      stack storage =>
    have hget : ((runtime dp).main :: (runtime dp).aux)[collisionRefusalSlot]? =
        some Func.rev := by
      simp [runtime, aux, baseAux, collisionRefusalSlot]
    exact (Func.RunCompiledTo.not_ok_call_rev hget callRun).elim

end LidoTriggerableWithdrawalsGateway
end Blanc
