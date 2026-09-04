import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute

/-!
# Exact TWG `onlyRole` routes

The gateway's role gate is shared by pause, resume, role mutation, and limit
management endpoints. This family-local seam inverts its nested-keccak key,
single membership read and guard once. It classifies an arbitrary terminal
outcome as either the authorized body walk or the compact missing-role call.
Every route retains the surviving stack tail and storage preservation across
the read-only prefix.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

/-- Sufficient calldata forces the live arm of the gateway's static-argument
guard. The result is outcome-polymorphic so authorization and success proofs
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
      (Func.revert <?> body)) out at run
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

/-- The two exact continuations of the gateway's one-read `onlyRole` modifier. -/
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
      (membershipZero : pre.getStorVal sevm.currentTarget
        (roleMembershipSlot role sevm.caller.toB256) = 0)
      (callRun : Func.RunCompiledTo
        ((runtime dp).main :: (runtime dp).aux) sevm callPre
          (.call missingRoleSlot) out)
      (stack : tail <<+ callPre.stack)
      (storage : Devm.getStor pre = Devm.getStor callPre)

/-- Peel the family's canonical-address argument guard at an arbitrary
outcome. An address-shaped argument word makes the masked test zero, which is
the falling-through arm; a dirty word takes the revert arm instead. -/
theorem canonicalArg_body_of_valid
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {index : B256} {body : Func} {tail : Stack}
    (hvalid : ValidAdr (Sevm.argWord sevm index))
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (canonicalArg index body) out) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre body out ∧
      tail <<+ bodyPre.stack ∧
      Devm.getStor pre = Devm.getStor bodyPre := by
  unfold canonicalArg at run
  obtain ⟨guardPost, guardLine, branchRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨y, pGuard, hiff⟩ := prefix_of_argCheckNonAddress hp guardLine
  rw [hiff.mpr hvalid] at pGuard
  obtain ⟨bodyPre, hpop, bodyRun, pBody⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pGuard branchRun
  have guardStor : Devm.getStor pre = Devm.getStor guardPost :=
    Line.of_inv Devm.getStor (by line_inv) guardLine
  exact ⟨bodyPre, bodyRun, pBody,
    guardStor.trans (funext (getStor_eq_of_state_eq hpop.state))⟩

/-- Exact arbitrary-outcome traversal of the shared one-read `onlyRole`
modifier. The key witness is the executable nested-keccak walk itself; raw
storage layout is not elevated into the public semantic predicate. -/
theorem onlyRole_route
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {role : B256} {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (onlyRole role body) out) :
    OnlyRoleRoute dp sevm pre role body tail out := by
  unfold onlyRole at run
  obtain ⟨loadPre, keyRun, run⟩ := runCompiledTo_prepend_inv run
  have pKey : roleMembershipSlot role sevm.caller.toB256 :: tail <<+
      loadPre.stack := prefix_of_viewRoleMembershipSlotForCaller hp keyRun
  obtain ⟨loadPost, qload, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have rload := Ninst.Run.of_runCompiled qload
  have rzero := Ninst.Run.of_runCompiled qzero
  obtain ⟨membership, pMembership, membershipRead⟩ :=
    prefix_of_sload rload pKey
  have pTest := prefix_of_iszero rzero pMembership
  have keyStor : Devm.getStor pre = Devm.getStor loadPre :=
    Line.of_inv Devm.getStor (by line_inv) keyRun
  have membershipAtEntry : membership =
      pre.getStorVal sevm.currentTarget
        (roleMembershipSlot role sevm.caller.toB256) := by
    rw [membershipRead]
    change (Devm.getStor loadPre sevm.currentTarget).get
        (roleMembershipSlot role sevm.caller.toB256) =
      (Devm.getStor pre sevm.currentTarget).get
        (roleMembershipSlot role sevm.caller.toB256)
    rw [← congrFun keyStor sevm.currentTarget]
  by_cases hnonzero : membership ≠ 0
  · have pZero : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.eqCheck, hnonzero] using pTest
    obtain ⟨bodyPre, hpop, bodyRun, pBody⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
    have bodyStor : Devm.getStor pre = Devm.getStor bodyPre :=
      keyStor.trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rload).trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rzero).trans
            (funext (getStor_eq_of_state_eq hpop.state))))
    have hasRole : CallerHasRole (Devm.getStor pre sevm.currentTarget)
        role sevm.caller.toB256 := by
      refine callerHasRole_exact_lookup ?_
      change pre.getStorVal sevm.currentTarget
        (roleMembershipSlot role sevm.caller.toB256) ≠ 0
      rw [← membershipAtEntry]
      exact hnonzero
    exact .authorized bodyPre hasRole bodyRun pBody bodyStor
  · have hzero : membership = 0 := by simpa using hnonzero
    have pOne : (1 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.eqCheck, hzero] using pTest
    obtain ⟨callPre, _, -, hpop, callRun, pCall⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) pOne branchRun
    have callStor : Devm.getStor pre = Devm.getStor callPre :=
      keyStor.trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rload).trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rzero).trans
            (funext (getStor_eq_of_state_eq hpop.state))))
    have entryZero : pre.getStorVal sevm.currentTarget
        (roleMembershipSlot role sevm.caller.toB256) = 0 :=
      membershipAtEntry.symm.trans hzero
    exact .missingRole callPre entryZero callRun pCall callStor

/-- A successful `onlyRole` traversal reaches the protected body and proves
the executable nested-keccak membership at the modifier entry. -/
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
  | missingRole callPre membershipZero callRun stack storage =>
    have hget : ((runtime dp).main :: (runtime dp).aux)[missingRoleSlot]? =
        some (runtimeError "AccessControlUnauthorizedAccount" []) := by
      simp [runtime, aux, baseAux, missingRoleSlot]
    exact (Func.RunCompiledTo.not_ok_call_revertSelector
      (by simpa [runtimeError] using hget) callRun).elim

end LidoTriggerableWithdrawalsGateway
end Blanc
