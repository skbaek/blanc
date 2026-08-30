import Blanc.ProxyPairOssifiableProgram
import Blanc.LinearDispatchCorrectness
import Blanc.CompiledWalkInversion

/-!
# Lido OssifiableProxy compiled control-plane routes

This module starts the semantic proof of the seven named runtime entries at
the compiled-program boundary.  It inverts the actual `Prog.RunCompiledTo`
entry burn, selector load, and linear dispatcher; it then opens the selected
auxiliary call to the concrete endpoint body.  The route is outcome-polymorphic
and therefore supports successful, reverting, and exceptional endpoint proofs.

The helper for nonzero-value `nonpayable` walks is contract-neutral and is
staged separately for its common owner, `Blanc.CompiledWalkInversion`; the
product theorems below are consumers only.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Blanc.Ninst
open scoped LogOutputHinv

namespace ProxyPair

/-! ## Exact runtime selection -/

/-- The concrete seven-entry table has no selector collision. -/
theorem runtimeBaselineEntries_selectorUnique :
    selectorUnique runtimeBaselineEntries := by
  simp [selectorUnique, runtimeBaselineEntries,
    proxyGetAdminSelector, proxyGetImplementationSelector,
    proxyGetIsOssifiedSelector, proxyOssifySelector,
    proxyChangeAdminSelector, proxyUpgradeToSelector,
    proxyUpgradeToAndCallSelector]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem fsig_dispatchFrame
    {entry mid afterSig : Devm} {sevm : Sevm}
    (hburn : Devm.BurnBy gJumpdest entry mid)
    (hsig : Line.Run sevm mid fsig afterSig) :
    Devm.DispatchFramePreserved entry afterSig := by
  unfold fsig cdl shiftRight at hsig
  rcases Line.of_run_cons hsig with ⟨sigPush, qpush0, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigLoad, qload, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigShift, qpush224, hsig⟩
  rcases Line.of_run_cons hsig with ⟨_, qshr, hnil⟩
  cases hnil
  rcases of_run_reg qload with ⟨_, qloadCore⟩
  simp only [Rinst.run, Rinst.runCore] at qloadCore
  rcases Except.bind_eq_ok qloadCore with
    ⟨⟨loadOffset, loadPop⟩, qloadPop, qloadCore⟩
  rcases Except.bind_eq_ok qloadCore with
    ⟨loadBurn, qloadBurn, qloadPush⟩
  have qloadDiff : Devm.DiffBurn [loadOffset]
      [Sevm.dataWord sevm loadOffset] sigPush sigLoad :=
    Devm.diffBurn_of_pop_of_pushBurn (Devm.pop_of_pop qloadPop)
      (Devm.pushBurn_of_burn_of_push (Devm.burn_of_chargeGas qloadBurn)
        (Devm.push_of_push qloadPush))
  rcases of_run_reg qshr with ⟨_, qshrCore⟩
  simp only [Rinst.run, Rinst.runCore] at qshrCore
  rcases Devm.diffBurn_of_applyBinary qshrCore with ⟨_, _, qshrDiff⟩
  exact (dispatchFrame_of_burnBy hburn).trans
    ((dispatchFrame_of_pushBurn (of_run_pushB256 qpush0)).trans
      ((dispatchFrame_of_diffBurn qloadDiff).trans
        ((dispatchFrame_of_pushBurn (of_run_pushB256 qpush224)).trans
          (dispatchFrame_of_diffBurn qshrDiff))))

/-- An exact compiled program walk from an empty operand stack reaches the
selected `nonpayable (.call slot)` dispatcher body with that stack restored.
Every entry-frame field except stack and gas is preserved up to the selected
body. -/
theorem runtime_selected_body_of_prog_run_empty_frame
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector : B256} {body : Func}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = [])
    (hselector : Sevm.selector sevm = selector)
    (hmember : (selector, body) ∈ runtimeBaselineEntries) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre body out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo
    (runtimeBaseline.main :: runtimeBaseline.aux) sevm mid
    (fsig +++ linearDispatchWith fallbackSlot runtimeBaselineEntries) out
    at hmain
  obtain ⟨afterSig, hsig, hdispatch⟩ := runCompiledTo_prepend_inv hmain
  have hmidStack : mid.stack = [] := by
    rw [← hburn.stack]
    exact hentryStack
  have hsigForFrame := hsig
  unfold fsig cdl shiftRight at hsig
  rcases Line.of_run_cons hsig with ⟨sigPush, qpush0, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigLoad, qload, hsig⟩
  rcases Line.of_run_cons hsig with ⟨sigShift, qpush224, hsig⟩
  rcases Line.of_run_cons hsig with ⟨_, qshr, hnil⟩
  cases hnil
  have hpushStack : sigPush.stack = (0 : B256) :: [] :=
    stack_of_pushBurn (of_run_pushB256 qpush0) hmidStack
  have hloadDiff : ∃ x, Stack.Diff [x] [Sevm.dataWord sevm x]
      sigPush.stack sigLoad.stack := of_run_calldataload_val qload
  have hloadStack : sigLoad.stack = Sevm.dataWord sevm 0 :: [] :=
    stack_of_diffBurn_one hloadDiff hpushStack
  have hshiftStack : sigShift.stack =
      (224 : B256) :: Sevm.dataWord sevm 0 :: [] :=
    stack_of_pushBurn (of_run_pushB256 qpush224) hloadStack
  have hshrDiff : ∃ x y, Stack.Diff [x, y]
      [y >>> x.toNat] sigShift.stack afterSig.stack := by
    rcases of_run_reg qshr with ⟨_, hr⟩
    simp only [Rinst.run, Rinst.runCore] at hr
    rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hdiff⟩
    exact ⟨x, y, hdiff.stack⟩
  have hafterSigStack : afterSig.stack = selector :: [] := by
    have hs := stack_of_diffBurn_two hshrDiff hshiftStack
    rw [← hselector]
    exact hs
  have hwitness := dispatchBodyWitness_of_runCompiledTo
    runtimeBaselineEntries_selectorUnique hmember hafterSigStack hdispatch
  rcases hwitness with
    ⟨bodyPre, _, hbody, hbodyStack, hbodyFrame⟩
  exact ⟨bodyPre, hbody, hbodyStack,
    (fsig_dispatchFrame hburn hsigForFrame).trans hbodyFrame⟩

/-! ## Canonical selector images -/

theorem selector_of_proxyGetAdminCalldata {sevm : Sevm}
    (hdata : sevm.data = proxyGetAdminCalldata) :
    Sevm.selector sevm = proxyGetAdminSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := proxyGetAdminSelector) (tail := [])
  · rfl
  · simpa [proxyGetAdminCalldata] using hdata

theorem selector_of_proxyGetImplementationCalldata {sevm : Sevm}
    (hdata : sevm.data = proxyGetImplementationCalldata) :
    Sevm.selector sevm = proxyGetImplementationSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := proxyGetImplementationSelector) (tail := [])
  · rfl
  · simpa [proxyGetImplementationCalldata] using hdata

theorem selector_of_proxyGetIsOssifiedCalldata {sevm : Sevm}
    (hdata : sevm.data = proxyGetIsOssifiedCalldata) :
    Sevm.selector sevm = proxyGetIsOssifiedSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := proxyGetIsOssifiedSelector) (tail := [])
  · rfl
  · simpa [proxyGetIsOssifiedCalldata] using hdata

theorem selector_of_proxyOssifyCalldata {sevm : Sevm}
    (hdata : sevm.data = proxyOssifyCalldata) :
    Sevm.selector sevm = proxyOssifySelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := proxyOssifySelector) (tail := [])
  · rfl
  · simpa [proxyOssifyCalldata] using hdata

theorem selector_of_proxyChangeAdminCalldata {sevm : Sevm} {newAdmin : Adr}
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin) :
    Sevm.selector sevm = proxyChangeAdminSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := proxyChangeAdminSelector)
      (tail := newAdmin.toB256.toBytes)
  · rfl
  · simpa [proxyChangeAdminCalldata] using hdata

theorem selector_of_proxyUpgradeToCalldata
    {sevm : Sevm} {newImplementation : Adr}
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation) :
    Sevm.selector sevm = proxyUpgradeToSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := proxyUpgradeToSelector)
      (tail := newImplementation.toB256.toBytes)
  · rfl
  · simpa [proxyUpgradeToCalldata] using hdata

theorem selector_of_proxyUpgradeToAndCallCalldata
    {sevm : Sevm} {newImplementation : Adr}
    {setupCalldata : Bytes} {forceCall : Bool}
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    Sevm.selector sevm = proxyUpgradeToAndCallSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := proxyUpgradeToAndCallSelector)
      (tail := newImplementation.toB256.toBytes ++
        (96 : B256).toBytes ++
        (if forceCall then (1 : B256) else 0).toBytes ++
        abiBytesTail setupCalldata)
  · rfl
  · simpa [proxyUpgradeToAndCallCalldata, List.append_assoc] using hdata

/-! ## Authorization precedence at endpoint altitude -/

/-- Solidity's address-typed view of an arbitrary raw storage word.  This is
the exact word left by the runtime's low-160-bit `SHR; AND` schedule. -/
def canonicalAddressWord (word : B256) : B256 :=
  (~~~ addressMask) &&& word

private theorem lowAddressMask_eq :
    (~~~ (0 : B256)) >>> (96 : Nat).toB256.toNat = ~~~ addressMask := by
  rw [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)]
  rfl

private theorem prefix_of_lowAddressClean
    {sevm : Sevm} {pre post : Devm} {word : B256} {tail : Stack}
    (hp : word :: tail <<+ pre.stack)
    (run : Line.Run sevm pre
      [pushB256 0, Ninst.not, pushB256 (Nat.toB256 96), Ninst.shr,
        Ninst.and] post) :
    canonicalAddressWord word :: tail <<+ post.stack := by
  rcases Line.of_run_cons run with ⟨zeroPost, qzero, run⟩
  rcases Line.of_run_cons run with ⟨notPost, qnot, run⟩
  rcases Line.of_run_cons run with ⟨shiftPost, qshift, run⟩
  rcases Line.of_run_cons run with ⟨andPost, qshr, run⟩
  rcases Line.of_run_cons run with ⟨_, qand, hnil⟩
  cases hnil
  have pZero := prefix_of_push (of_run_pushB256 qzero) hp
  have pNot := prefix_of_not qnot pZero
  have pShift := prefix_of_push (of_run_pushB256 qshift) pNot
  have pShr := prefix_of_shr qshr pShift
  have pAnd := prefix_of_and qand pShr
  simpa only [canonicalAddressWord, lowAddressMask_eq] using pAnd

def storedAdminWord (devm : Devm) (owner : Adr) : B256 :=
  canonicalAddressWord (devm.getStorVal owner adminSlotLit)

def storedImplementationWord (devm : Devm) (owner : Adr) : B256 :=
  canonicalAddressWord (devm.getStorVal owner implementationSlotLit)

/-- Public proof vocabulary for the runtime's private `onlyActiveAdmin`
schedule.  The product definitions below are tied back to this schedule by
definitional equalities, so the route theorem cannot silently describe a
different authorization order. -/
def activeAdminControl (body : Func) : Func :=
  ([pushB256 adminSlotLit, sload, pushB256 0, Ninst.not,
      pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and]) +++
    (dup 0 ::: iszero :::
      ((.call proxyIsOssifiedErrorSlot) <?>
        (caller ::: eq ::: (body <?> (.call notAdminErrorSlot)))))

/-- The three exhaustive routes through `onlyActiveAdmin`.  The ossified route
is tested first and therefore carries no caller-comparison premise. -/
inductive ActiveAdminRoute
    (fs : List Func) (sevm : Sevm) (pre : Devm)
    (body : Func) (tail : Stack) (out : Execution) : Prop
  | ossified (callPre : Devm)
      (adminZero : storedAdminWord pre sevm.currentTarget = 0)
      (callRun : Func.RunCompiledTo fs sevm callPre
        (.call proxyIsOssifiedErrorSlot) out)
      (stack : storedAdminWord pre sevm.currentTarget :: tail <<+
        callPre.stack)
      (storage : Devm.getStor pre = Devm.getStor callPre)
      (memory : pre.memory = callPre.memory)
      (logs : pre.logs = callPre.logs)
  | authorized (bodyPre : Devm)
      (adminNonzero : storedAdminWord pre sevm.currentTarget ≠ 0)
      (adminEqCaller : storedAdminWord pre sevm.currentTarget =
        sevm.caller.toB256)
      (bodyRun : Func.RunCompiledTo fs sevm bodyPre body out)
      (stack : tail <<+ bodyPre.stack)
      (storage : Devm.getStor pre = Devm.getStor bodyPre)
      (memory : pre.memory = bodyPre.memory)
      (logs : pre.logs = bodyPre.logs)
  | unauthorized (callPre : Devm)
      (adminNonzero : storedAdminWord pre sevm.currentTarget ≠ 0)
      (adminNeCaller : storedAdminWord pre sevm.currentTarget ≠
        sevm.caller.toB256)
      (callRun : Func.RunCompiledTo fs sevm callPre
        (.call notAdminErrorSlot) out)
      (stack : tail <<+ callPre.stack)
      (storage : Devm.getStor pre = Devm.getStor callPre)
      (memory : pre.memory = callPre.memory)
      (logs : pre.logs = callPre.logs)

/-- Exact, arbitrary-outcome inversion of the active-admin schedule. -/
theorem activeAdminControl_route
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (activeAdminControl body) out) :
    ActiveAdminRoute fs sevm pre body tail out := by
  unfold activeAdminControl at run
  obtain ⟨guardPre, guardLine, run⟩ := runCompiledTo_prepend_inv run
  have guardStor : Devm.getStor pre = Devm.getStor guardPre :=
    Line.of_inv Devm.getStor (by line_inv) guardLine
  have guardMemory : pre.memory = guardPre.memory :=
    Line.of_inv Devm.memory (by line_inv) guardLine
  have guardLogs : pre.logs = guardPre.logs :=
    Line.of_inv Devm.logs (by line_inv) guardLine
  obtain ⟨loadPost, headLine, cleanLine⟩ :=
    of_run_append [pushB256 adminSlotLit, sload] guardLine
  rcases Line.of_run_cons headLine with ⟨slotPost, qslot, headLine⟩
  rcases Line.of_run_cons headLine with ⟨_, qload, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨rawAdmin, pRawAdmin, hRawAdmin⟩ :=
    prefix_of_sload qload pSlot
  have pAdmin0 := prefix_of_lowAddressClean pRawAdmin cleanLine
  have pAdmin : storedAdminWord pre sevm.currentTarget :: tail <<+
      guardPre.stack := by
    have slotStor : Devm.getStor pre = Devm.getStor slotPost :=
      Ninst.Hinv.inv (f := Devm.getStor) qslot
    have hraw : rawAdmin = pre.getStorVal sevm.currentTarget adminSlotLit := by
      rw [hRawAdmin]
      change (Devm.getStor slotPost sevm.currentTarget).get adminSlotLit =
        (Devm.getStor pre sevm.currentTarget).get adminSlotLit
      rw [← congrFun slotStor sevm.currentTarget]
    simpa [storedAdminWord, canonicalAddressWord, hraw] using pAdmin0
  obtain ⟨dupPost, qdup, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, outerBranch⟩ := runCompiledTo_next_inv run
  have pDup := prefix_of_dup_val (Ninst.Run.of_runCompiled qdup)
    (Stack.Nth.head _ _) pAdmin
  have pTest := prefix_of_iszero (Ninst.Run.of_runCompiled qzero) pDup
  by_cases hzero : storedAdminWord pre sevm.currentTarget = 0
  · have pOne : (1 : B256) ::
        storedAdminWord pre sevm.currentTarget :: tail <<+ testPre.stack := by
      simpa [hzero, B256.eqCheck] using pTest
    obtain ⟨callPre, _, _, hpop, callRun, pCall⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) pOne outerBranch
    have callStor : Devm.getStor pre = Devm.getStor callPre :=
      guardStor.trans
        ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled qdup)).trans
          ((Ninst.Hinv.inv (f := Devm.getStor)
            (Ninst.Run.of_runCompiled qzero)).trans
            (funext (getStor_eq_of_state_eq hpop.state))))
    have callMemory : pre.memory = callPre.memory :=
      guardMemory.trans
        ((Ninst.Hinv.inv (f := Devm.memory)
          (Ninst.Run.of_runCompiled qdup)).trans
          ((Ninst.Hinv.inv (f := Devm.memory)
            (Ninst.Run.of_runCompiled qzero)).trans hpop.memory))
    have callLogs : pre.logs = callPre.logs :=
      guardLogs.trans
        ((Ninst.Hinv.inv (f := Devm.logs)
          (Ninst.Run.of_runCompiled qdup)).trans
          ((Ninst.Hinv.inv (f := Devm.logs)
            (Ninst.Run.of_runCompiled qzero)).trans hpop.logs))
    exact .ossified callPre hzero callRun pCall callStor callMemory callLogs
  · have pZero : (0 : B256) ::
        storedAdminWord pre sevm.currentTarget :: tail <<+ testPre.stack := by
      simpa [B256.eqCheck, hzero] using pTest
    obtain ⟨callerPre, houterPop, callerRun, pCallerPre⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pZero outerBranch
    obtain ⟨callerPost, qcaller, callerRun⟩ :=
      runCompiledTo_next_inv callerRun
    obtain ⟨callerTest, qeq, callerBranch⟩ :=
      runCompiledTo_next_inv callerRun
    have pCaller := prefix_of_push
      (of_run_caller (Ninst.Run.of_runCompiled qcaller)) pCallerPre
    have pEq := prefix_of_eq (Ninst.Run.of_runCompiled qeq) pCaller
    have prefixStor : Devm.getStor pre = Devm.getStor callerTest :=
      guardStor.trans
        ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled qdup)).trans
          ((Ninst.Hinv.inv (f := Devm.getStor)
            (Ninst.Run.of_runCompiled qzero)).trans
            ((funext (getStor_eq_of_state_eq houterPop.state)).trans
              ((Ninst.Hinv.inv (f := Devm.getStor)
                (Ninst.Run.of_runCompiled qcaller)).trans
                (Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled qeq))))))
    have prefixMemory : pre.memory = callerTest.memory :=
      guardMemory.trans
        ((Ninst.Hinv.inv (f := Devm.memory)
          (Ninst.Run.of_runCompiled qdup)).trans
          ((Ninst.Hinv.inv (f := Devm.memory)
            (Ninst.Run.of_runCompiled qzero)).trans
            (houterPop.memory.trans
              ((Ninst.Hinv.inv (f := Devm.memory)
                (Ninst.Run.of_runCompiled qcaller)).trans
                (Ninst.Hinv.inv (f := Devm.memory)
                  (Ninst.Run.of_runCompiled qeq))))))
    have prefixLogs : pre.logs = callerTest.logs :=
      guardLogs.trans
        ((Ninst.Hinv.inv (f := Devm.logs)
          (Ninst.Run.of_runCompiled qdup)).trans
          ((Ninst.Hinv.inv (f := Devm.logs)
            (Ninst.Run.of_runCompiled qzero)).trans
            (houterPop.logs.trans
              ((Ninst.Hinv.inv (f := Devm.logs)
                (Ninst.Run.of_runCompiled qcaller)).trans
                (Ninst.Hinv.inv (f := Devm.logs)
                  (Ninst.Run.of_runCompiled qeq))))))
    by_cases heq : storedAdminWord pre sevm.currentTarget =
        sevm.caller.toB256
    · have pOne : (1 : B256) :: tail <<+ callerTest.stack := by
        simpa [heq, B256.eqCheck] using pEq
      obtain ⟨bodyPre, _, _, hpop, bodyRun, pBody⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pOne callerBranch
      exact .authorized bodyPre hzero heq bodyRun pBody
        (prefixStor.trans (funext (getStor_eq_of_state_eq hpop.state)))
        (prefixMemory.trans hpop.memory) (prefixLogs.trans hpop.logs)
    · have pZero : (0 : B256) :: tail <<+ callerTest.stack := by
        simpa [B256.eqCheck, Ne.symm heq] using pEq
      obtain ⟨callPre, hpop, callRun, pCall⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pZero callerBranch
      exact .unauthorized callPre hzero heq callRun pCall
        (prefixStor.trans (funext (getStor_eq_of_state_eq hpop.state)))
        (prefixMemory.trans hpop.memory) (prefixLogs.trans hpop.logs)

/-- Once the stored admin is zero, the active-admin schedule can only reach
the `ProxyIsOssified` boundary.  Caller equality is deliberately absent. -/
theorem ActiveAdminRoute.ossified_of_admin_zero
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {out : Execution}
    (adminZero : storedAdminWord pre sevm.currentTarget = 0)
    (route : ActiveAdminRoute fs sevm pre body tail out) :
    ∃ callPre,
      Func.RunCompiledTo fs sevm callPre
        (.call proxyIsOssifiedErrorSlot) out := by
  cases route with
  | ossified callPre _ callRun _ _ _ _ => exact ⟨callPre, callRun⟩
  | authorized _ adminNonzero _ _ _ _ _ _ =>
      exact (adminNonzero adminZero).elim
  | unauthorized _ adminNonzero _ _ _ _ _ _ =>
      exact (adminNonzero adminZero).elim

/-- A live matching admin forces the protected body arm. -/
theorem ActiveAdminRoute.authorized_of_live_caller
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {out : Execution}
    (adminNonzero : storedAdminWord pre sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord pre sevm.currentTarget =
      sevm.caller.toB256)
    (route : ActiveAdminRoute fs sevm pre body tail out) :
    ∃ bodyPre,
      Func.RunCompiledTo fs sevm bodyPre body out ∧
      tail <<+ bodyPre.stack := by
  cases route with
  | ossified _ adminZero _ _ _ _ _ =>
      exact (adminNonzero adminZero).elim
  | authorized bodyPre _ _ bodyRun stack _ _ _ =>
      exact ⟨bodyPre, bodyRun, stack⟩
  | unauthorized _ _ adminNeCaller _ _ _ _ _ =>
      exact (adminNeCaller adminEqCaller).elim

/-- A live mismatching admin forces the `NotAdmin` boundary. -/
theorem ActiveAdminRoute.notAdmin_of_live_mismatch
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {out : Execution}
    (adminNonzero : storedAdminWord pre sevm.currentTarget ≠ 0)
    (adminNeCaller : storedAdminWord pre sevm.currentTarget ≠
      sevm.caller.toB256)
    (route : ActiveAdminRoute fs sevm pre body tail out) :
    ∃ callPre,
      Func.RunCompiledTo fs sevm callPre (.call notAdminErrorSlot) out := by
  cases route with
  | ossified _ adminZero _ _ _ _ _ =>
      exact (adminNonzero adminZero).elim
  | authorized _ _ adminEqCaller _ _ _ _ _ =>
      exact (adminNeCaller adminEqCaller).elim
  | unauthorized callPre _ _ callRun _ _ _ _ => exact ⟨callPre, callRun⟩

/-! ## Canonical static-address decoder -/

/-- Public proof vocabulary for the runtime's private one-address ABI decoder. -/
def decodeAddressArg0Control (body : Func) : Func :=
  pushB256 36 ::: calldatasize ::: lt :::
  ((.call emptyRevertSlot) <?>
    ((arg 0 ++ checkNonAddress) +++
      ((.call emptyRevertSlot) <?> body)))

/-- Sufficient calldata and a canonical address word reach the protected body
at an arbitrary outcome.  The decoder is read-only up to that body. -/
theorem decodeAddressArg0Control_body
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hsize : B256.ltCheck sevm.data.length.toB256 (36 : B256) = 0)
    (hvalid : ValidAdr (Sevm.argWord sevm 0))
    (run : Func.RunCompiledTo fs sevm pre
      (decodeAddressArg0Control body) out) :
    ∃ bodyPre,
      Func.RunCompiledTo fs sevm bodyPre body out ∧
      tail <<+ bodyPre.stack ∧
      Devm.getStor pre = Devm.getStor bodyPre := by
  unfold decodeAddressArg0Control at run
  obtain ⟨sizeTest, qword, run⟩ := runCompiledTo_next_inv run
  obtain ⟨sizePost, qsize, run⟩ := runCompiledTo_next_inv run
  obtain ⟨sizeBranchPre, qlt, sizeBranch⟩ := runCompiledTo_next_inv run
  have pWord := prefix_of_push
    (of_run_pushB256 (Ninst.Run.of_runCompiled qword)) hp
  have pSize := prefix_of_push
    (of_run_calldatasize (Ninst.Run.of_runCompiled qsize)) pWord
  have pLt := prefix_of_lt (Ninst.Run.of_runCompiled qlt) pSize
  have pSizeZero : (0 : B256) :: tail <<+ sizeBranchPre.stack := by
    simpa [hsize] using pLt
  obtain ⟨addressGuardPre, hsizePop, addressGuardRun, pAddressGuard⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pSizeZero sizeBranch
  obtain ⟨addressTest, addressLine, addressBranch⟩ :=
    runCompiledTo_prepend_inv addressGuardRun
  obtain ⟨dirty, pDirty, hdirty⟩ :=
    prefix_of_argCheckNonAddress pAddressGuard addressLine
  have hdirtyZero : dirty = 0 := hdirty.mpr hvalid
  have pAddressZero : (0 : B256) :: tail <<+ addressTest.stack := by
    simpa [hdirtyZero] using pDirty
  obtain ⟨bodyPre, haddressPop, bodyRun, pBody⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pAddressZero addressBranch
  have prefixStor : Devm.getStor pre = Devm.getStor addressGuardPre :=
    (Ninst.Hinv.inv (f := Devm.getStor)
      (Ninst.Run.of_runCompiled qword)).trans
      ((Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled qsize)).trans
        ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled qlt)).trans
          (funext (getStor_eq_of_state_eq hsizePop.state))))
  exact ⟨bodyPre, bodyRun, pBody,
    prefixStor.trans
      ((Line.of_inv Devm.getStor (by line_inv) addressLine).trans
        (funext (getStor_eq_of_state_eq haddressPop.state)))⟩

/-! ## `upgradeToAndCall` proof-facing decoder and setup tail -/

/-- Product-local names for the four scratch words used by the compiled
`upgradeToAndCall` decoder.  These are proof coordinates, not common ABI
vocabulary. -/
def upgradeToAndCallImplementationWord : B256 := 0
def upgradeToAndCallSetupLengthWord : B256 := 1
def upgradeToAndCallForceWord : B256 := 2
def upgradeToAndCallOffsetWord : B256 := 3

/-- The decoded setup bytes begin immediately above the four scratch words. -/
def upgradeToAndCallSetupMemoryBase : B256 := 0x80

def upgradeToAndCallAbiMaxUint64 : B256 := 0xffffffffffffffff

def loadUpgradeToAndCallWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

/-- Public proof vocabulary for the runtime's private `(address,bytes,bool)`
decoder.  The definition is intentionally product-local and definitionally
equal to the executable schedule. -/
def decodeUpgradeToAndCallControl (body : Func) : Func :=
  pushB256 100 ::: calldatasize ::: lt :::
  ((.call emptyRevertSlot) <?>
    (arg 0 +++ checkNonAddress +++
     ((.call emptyRevertSlot) <?>
       (arg 0 +++ mstoreAt upgradeToAndCallImplementationWord +++
        pushB256 upgradeToAndCallAbiMaxUint64 ::: arg 1 +++ gt :::
        ((.call emptyRevertSlot) <?>
          (arg 1 +++ mstoreAt upgradeToAndCallOffsetWord +++
           loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
             pushB256 36 ::: add ::: calldatasize ::: lt :::
           ((.call emptyRevertSlot) <?>
             (loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
                pushB256 4 ::: add ::: calldataload :::
                mstoreAt upgradeToAndCallSetupLengthWord +++
              pushB256 upgradeToAndCallAbiMaxUint64 :::
                loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++
                gt :::
              ((.call allocationPanicSlot) <?>
                (loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
                   pushB256 36 ::: add :::
                 loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++
                   add :::
                 calldatasize ::: lt :::
                 ((.call emptyRevertSlot) <?>
                   (loadUpgradeToAndCallWord
                        upgradeToAndCallSetupLengthWord +++
                    loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
                      pushB256 36 ::: add :::
                    pushB256 upgradeToAndCallSetupMemoryBase :::
                      calldatacopy :::
                    arg 2 +++ dup 0 ::: iszero ::: iszero ::: eq :::
                    ((arg 2 +++ mstoreAt upgradeToAndCallForceWord +++ body) <?>
                      (.call emptyRevertSlot))))))))))))))

/-- The exact decoded setup call.  The output window is empty; child
returndata is retained only in `returnData` for the following failure arm. -/
def upgradeToAndCallDelegateSetup : Func :=
  pushB256 0 :::
  pushB256 0 :::
  loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++
  pushB256 upgradeToAndCallSetupMemoryBase :::
  loadUpgradeToAndCallWord upgradeToAndCallImplementationWord +++
  gas ::: delcall :::
  (Func.stop <?>
    (retdatasize :::
      (Func.revReturnData <?> (.call emptyDelegatecallErrorSlot))))

/-- The three setup branches: nonempty data calls unconditionally; empty data
calls exactly when the decoded force word is nonzero. -/
def upgradeToAndCallAfter : Func :=
  loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++
  (upgradeToAndCallDelegateSetup <?>
    (loadUpgradeToAndCallWord upgradeToAndCallForceWord +++
      (upgradeToAndCallDelegateSetup <?> Func.stop)))

theorem proxyChangeAdminCalldata_length (newAdmin : Adr) :
    (proxyChangeAdminCalldata newAdmin).length = 36 := by
  simp [proxyChangeAdminCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

theorem proxyUpgradeToCalldata_length (newImplementation : Adr) :
    (proxyUpgradeToCalldata newImplementation).length = 36 := by
  simp [proxyUpgradeToCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

theorem proxyChangeAdminCalldata_arg0
    {sevm : Sevm} {newAdmin : Adr}
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin) :
    Sevm.argWord sevm 0 = newAdmin.toB256 := by
  change Sevm.dataWord sevm 4 = newAdmin.toB256
  apply dataWord_of_append
    (pre := abiSelectorBytes proxyChangeAdminSelector) (post := [])
  · rw [abiSelectorBytes_length]
    rfl
  · simpa [proxyChangeAdminCalldata] using hdata

theorem proxyUpgradeToCalldata_arg0
    {sevm : Sevm} {newImplementation : Adr}
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation) :
    Sevm.argWord sevm 0 = newImplementation.toB256 := by
  change Sevm.dataWord sevm 4 = newImplementation.toB256
  apply dataWord_of_append
    (pre := abiSelectorBytes proxyUpgradeToSelector) (post := [])
  · rw [abiSelectorBytes_length]
    rfl
  · simpa [proxyUpgradeToCalldata] using hdata

theorem proxyUpgradeToAndCallCalldata_length
    (newImplementation : Adr) (setupCalldata : Bytes) (forceCall : Bool) :
    (proxyUpgradeToAndCallCalldata newImplementation setupCalldata forceCall).length =
      132 + ceil32 setupCalldata.length := by
  have hceil := Nat.le_ceil32 setupCalldata.length
  simp [proxyUpgradeToAndCallCalldata, abiBytesTail,
    abiSelectorBytes_length, B256.length_toBytes]
  omega

theorem proxyUpgradeToAndCallCalldata_arg0
    {sevm : Sevm} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool}
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    Sevm.argWord sevm 0 = newImplementation.toB256 := by
  change Sevm.dataWord sevm 4 = newImplementation.toB256
  apply dataWord_of_append
    (pre := abiSelectorBytes proxyUpgradeToAndCallSelector)
  · rw [abiSelectorBytes_length]
    rfl
  · simpa [proxyUpgradeToAndCallCalldata, List.append_assoc] using hdata

theorem proxyUpgradeToAndCallCalldata_arg1
    {sevm : Sevm} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool}
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    Sevm.argWord sevm 1 = 96 := by
  change Sevm.dataWord sevm 36 = (96 : B256)
  apply dataWord_of_append
    (pre := abiSelectorBytes proxyUpgradeToAndCallSelector ++
      newImplementation.toB256.toBytes)
  · simp [abiSelectorBytes_length, B256.length_toBytes]
    decide +kernel
  · simpa [proxyUpgradeToAndCallCalldata, List.append_assoc] using hdata

theorem proxyUpgradeToAndCallCalldata_arg2
    {sevm : Sevm} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool}
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    Sevm.argWord sevm 2 = if forceCall then 1 else 0 := by
  change Sevm.dataWord sevm 68 = (if forceCall then 1 else 0)
  apply dataWord_of_append
    (pre := abiSelectorBytes proxyUpgradeToAndCallSelector ++
      newImplementation.toB256.toBytes ++ (96 : B256).toBytes)
  · simp [abiSelectorBytes_length, B256.length_toBytes]
    decide +kernel
  · simpa [proxyUpgradeToAndCallCalldata, List.append_assoc] using hdata

theorem proxyUpgradeToAndCallCalldata_setupLength
    {sevm : Sevm} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool}
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    Sevm.dataWord sevm 100 = Nat.toB256 setupCalldata.length := by
  apply dataWord_of_append
    (pre := abiSelectorBytes proxyUpgradeToAndCallSelector ++
      newImplementation.toB256.toBytes ++ (96 : B256).toBytes ++
      (if forceCall then (1 : B256) else 0).toBytes)
  · simp [abiSelectorBytes_length, B256.length_toBytes]
    decide +kernel
  · simpa [proxyUpgradeToAndCallCalldata, abiBytesTail,
      List.append_assoc] using hdata

theorem proxyUpgradeToAndCallCalldata_setupSlice
    {sevm : Sevm} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool}
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    sevm.data.sliceD 132 setupCalldata.length 0 = setupCalldata := by
  have hd : sevm.data =
      (abiSelectorBytes proxyUpgradeToAndCallSelector ++
        newImplementation.toB256.toBytes ++ (96 : B256).toBytes ++
        (if forceCall then (1 : B256) else 0).toBytes ++
        (Nat.toB256 setupCalldata.length).toBytes) ++
      (setupCalldata ++
        List.replicate (ceil32 setupCalldata.length - setupCalldata.length) 0) := by
    simpa [proxyUpgradeToAndCallCalldata, abiBytesTail,
      List.append_assoc] using hdata
  rw [hd, List.sliceD,
    List.drop_length_append' (by
      simp [abiSelectorBytes_length, B256.length_toBytes]),
    List.takeD_eq_take _ (by simp [List.length_append]),
    List.take_length_append' rfl]

/-! ## Exact source-shape locks used by route consumers -/

theorem getAdmin_control_shape :
    getAdmin =
      ([pushB256 adminSlotLit, sload, pushB256 0, Ninst.not,
        pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and]) +++
      (mstoreAt 0 +++ returnMemoryRange 0 32) := by
  rfl

theorem getImplementation_control_shape :
    getImplementation =
      ([pushB256 implementationSlotLit, sload, pushB256 0, Ninst.not,
        pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and]) +++
      (mstoreAt 0 +++ returnMemoryRange 0 32) := by
  rfl

theorem getIsOssified_control_shape :
    getIsOssified =
      ([pushB256 adminSlotLit, sload, pushB256 0, Ninst.not,
        pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and,
        Ninst.iszero]) +++
      (mstoreAt 0 +++ returnMemoryRange 0 32) := by
  rfl

def changeAdminMutation : Func :=
  ([pushB256 adminSlotLit, sload, pushB256 0, Ninst.not,
      pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and]) +++
    (mstoreAt 0 +++
      arg 0 +++ mstoreAt 1 +++
      pushB256 adminChangedEventTopic ::: logWith 0 0 2 +++
      arg 0 +++ iszero :::
      ((.call zeroAdminErrorSlot) <?>
        (arg 0 +++ storeAddressWordAt adminSlotLit +++ Func.stop)))

def upgradeImplementationControl (continuation : Func) : Func :=
  arg 0 +++ dup 0 ::: extcodesize ::: iszero :::
  ((.call noCodeImplementationErrorSlot) <?>
    (dup 0 ::: storeAddressWordAt implementationSlotLit +++
      pushB256 upgradedEventTopic ::: logWith 1 0 0 +++
      continuation))

theorem changeAdmin_control_shape :
    changeAdmin = decodeAddressArg0Control
      (activeAdminControl changeAdminMutation) := by
  rfl

theorem upgradeTo_control_shape :
    upgradeTo = decodeAddressArg0Control
      (activeAdminControl (upgradeImplementationControl Func.stop)) := by
  rfl

theorem upgradeToAndCall_control_shape :
    upgradeToAndCall = decodeUpgradeToAndCallControl
      (activeAdminControl
        (upgradeImplementationControl upgradeToAndCallAfter)) := by
  rfl

def ossifyMutation : Func :=
  [pushB256 adminSlotLit, sload] +++
  ([pushB256 0, Ninst.not, pushB256 (Nat.toB256 96), Ninst.shr,
      Ninst.and] +++ (mstoreAt 0 +++
    pushB256 0 ::: storeAddressWordAt adminSlotLit +++
    pushB256 0 ::: mstoreAt 1 +++
    pushB256 adminChangedEventTopic ::: logWith 0 0 2 +++
    pushB256 proxyOssifiedEventTopic ::: logWith 0 0 0 +++
    Func.stop))

theorem ossify_control_shape :
    ossify = activeAdminControl ossifyMutation := by
  rfl

/-! ## Exact successful getter bodies -/

/-- The successful `proxy__getAdmin()` body returns the canonical low-160-bit
view of the admin slot.  The result is stated over the actual compiled body;
`ReturnsWord` fixes all 32 output bytes. -/
theorem getAdmin_successful_body_returns
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre getAdmin (.ok post)) :
    ReturnsWord (storedAdminWord pre sevm.currentTarget) post := by
  have sourceRun : Func.Run fs sevm pre getAdmin post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  rw [getAdmin_control_shape] at sourceRun
  obtain ⟨returnPre, readLine, returnRun⟩ :=
    of_run_prepend
      [pushB256 adminSlotLit, sload, pushB256 0, Ninst.not,
        pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and] _ sourceRun
  obtain ⟨loadPost, headLine, cleanLine⟩ :=
    of_run_append [pushB256 adminSlotLit, sload] readLine
  rcases Line.of_run_cons headLine with ⟨slotPost, qslot, headLine⟩
  rcases Line.of_run_cons headLine with ⟨_, qload, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨rawAdmin, pRawAdmin, hRawAdmin⟩ :=
    prefix_of_sload qload pSlot
  have pAdmin0 := prefix_of_lowAddressClean pRawAdmin cleanLine
  have pAdmin : storedAdminWord pre sevm.currentTarget :: tail <<+
      returnPre.stack := by
    have slotStor : Devm.getStor pre = Devm.getStor slotPost :=
      Ninst.Hinv.inv (f := Devm.getStor) qslot
    have hraw : rawAdmin = pre.getStorVal sevm.currentTarget adminSlotLit := by
      rw [hRawAdmin]
      change (Devm.getStor slotPost sevm.currentTarget).get adminSlotLit =
        (Devm.getStor pre sevm.currentTarget).get adminSlotLit
      rw [← congrFun slotStor sevm.currentTarget]
    simpa [storedAdminWord, canonicalAddressWord, hraw] using pAdmin0
  exact (returnsWord_of_storeReturn pAdmin returnRun).1

/-- The successful implementation getter has the same exact return shape at
the ERC-1967 implementation slot. -/
theorem getImplementation_successful_body_returns
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre getImplementation (.ok post)) :
    ReturnsWord (storedImplementationWord pre sevm.currentTarget) post := by
  have sourceRun : Func.Run fs sevm pre getImplementation post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  rw [getImplementation_control_shape] at sourceRun
  obtain ⟨returnPre, readLine, returnRun⟩ :=
    of_run_prepend
      [pushB256 implementationSlotLit, sload, pushB256 0, Ninst.not,
        pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and] _ sourceRun
  obtain ⟨loadPost, headLine, cleanLine⟩ :=
    of_run_append [pushB256 implementationSlotLit, sload] readLine
  rcases Line.of_run_cons headLine with ⟨slotPost, qslot, headLine⟩
  rcases Line.of_run_cons headLine with ⟨_, qload, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨rawImplementation, pRawImplementation, hRawImplementation⟩ :=
    prefix_of_sload qload pSlot
  have pImplementation0 :=
    prefix_of_lowAddressClean pRawImplementation cleanLine
  have pImplementation :
      storedImplementationWord pre sevm.currentTarget :: tail <<+
        returnPre.stack := by
    have slotStor : Devm.getStor pre = Devm.getStor slotPost :=
      Ninst.Hinv.inv (f := Devm.getStor) qslot
    have hraw : rawImplementation =
        pre.getStorVal sevm.currentTarget implementationSlotLit := by
      rw [hRawImplementation]
      change
        (Devm.getStor slotPost sevm.currentTarget).get implementationSlotLit =
          (Devm.getStor pre sevm.currentTarget).get implementationSlotLit
      rw [← congrFun slotStor sevm.currentTarget]
    simpa [storedImplementationWord, canonicalAddressWord, hraw] using
      pImplementation0
  exact (returnsWord_of_storeReturn pImplementation returnRun).1

/-- `proxy__getIsOssified()` is exactly the zero test of the canonical admin
word, encoded as a complete ABI word. -/
theorem getIsOssified_successful_body_returns
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre getIsOssified (.ok post)) :
    ReturnsWord (storedAdminWord pre sevm.currentTarget =? 0) post := by
  have sourceRun : Func.Run fs sevm pre getIsOssified post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  rw [getIsOssified_control_shape] at sourceRun
  obtain ⟨returnPre, readLine, returnRun⟩ :=
    of_run_prepend
      [pushB256 adminSlotLit, sload, pushB256 0, Ninst.not,
        pushB256 (Nat.toB256 96), Ninst.shr, Ninst.and,
        Ninst.iszero] _ sourceRun
  obtain ⟨loadPost, headLine, cleanLine⟩ :=
    of_run_append [pushB256 adminSlotLit, sload] readLine
  rcases Line.of_run_cons headLine with ⟨slotPost, qslot, headLine⟩
  rcases Line.of_run_cons headLine with ⟨_, qload, hnil⟩
  cases hnil
  obtain ⟨adminPost, cleanAddressLine, cleanTail⟩ :=
    of_run_append
      [pushB256 0, Ninst.not, pushB256 (Nat.toB256 96), Ninst.shr,
        Ninst.and] cleanLine
  rcases Line.of_run_cons cleanTail with ⟨_, qzero, hnil⟩
  cases hnil
  have pSlot := prefix_of_push (of_run_pushB256 qslot) hp
  obtain ⟨rawAdmin, pRawAdmin, hRawAdmin⟩ :=
    prefix_of_sload qload pSlot
  have pAdmin0 := prefix_of_lowAddressClean pRawAdmin cleanAddressLine
  have pAdmin : storedAdminWord pre sevm.currentTarget :: tail <<+
      adminPost.stack := by
    have slotStor : Devm.getStor pre = Devm.getStor slotPost :=
      Ninst.Hinv.inv (f := Devm.getStor) qslot
    have hraw : rawAdmin = pre.getStorVal sevm.currentTarget adminSlotLit := by
      rw [hRawAdmin]
      change (Devm.getStor slotPost sevm.currentTarget).get adminSlotLit =
        (Devm.getStor pre sevm.currentTarget).get adminSlotLit
      rw [← congrFun slotStor sevm.currentTarget]
    simpa [storedAdminWord, canonicalAddressWord, hraw] using pAdmin0
  have pFlag := prefix_of_iszero qzero pAdmin
  exact (returnsWord_of_storeReturn pFlag returnRun).1

/-! ## Endpoint body opening -/

/-- The selected dispatcher body and its auxiliary call are both opened, so
the result is a walk of the endpoint implementation itself.  This is the
common opening used by all seven public endpoint theorems below. -/
private theorem endpoint_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector : B256} {slot : Nat} {endpoint : Func}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector)
    (hmember : (selector, nonpayable (.call slot)) ∈
      runtimeBaselineEntries)
    (hslot :
      (runtimeBaseline.main :: runtimeBaseline.aux)[slot]? = some endpoint) :
    ∃ endpointPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm endpointPre endpoint out ∧
      ([] : Stack) <<+ endpointPre.stack ∧
      Devm.getStor entry = Devm.getStor endpointPre := by
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, dispatchFrame⟩ :=
    runtime_selected_body_of_prog_run_empty_frame hprog hentryStack hselector
      hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  obtain ⟨callPre, callRun, pCall, callStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_value_zero hvalue pDispatch
      dispatchRun
  obtain ⟨endpointPre, hcallBurn, endpointRun⟩ :=
    runCompiledTo_call_inv hslot callRun
  have pEndpoint : ([] : Stack) <<+ endpointPre.stack := by
    rw [← hcallBurn.stack]
    exact pCall
  exact ⟨endpointPre, endpointRun, pEndpoint,
    (funext (getStor_eq_of_state_eq dispatchFrame.state)).trans
      (callStor.trans (funext (getStor_eq_of_state_eq hcallBurn.state)))⟩

theorem getAdmin_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyGetAdminCalldata) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre getAdmin out ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.getStor entry = Devm.getStor bodyPre := by
  exact endpoint_body_of_program (slot := getAdminSlot) (endpoint := getAdmin)
    hprog hentryStack hvalue
    (selector_of_proxyGetAdminCalldata hdata) (by simp [runtimeBaselineEntries])
    (by simp [runtimeBaseline, runtimeBaselineAux, getAdminSlot])

theorem getImplementation_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyGetImplementationCalldata) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre getImplementation out ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.getStor entry = Devm.getStor bodyPre := by
  exact endpoint_body_of_program (slot := getImplementationSlot)
    (endpoint := getImplementation) hprog hentryStack hvalue
    (selector_of_proxyGetImplementationCalldata hdata)
    (by simp [runtimeBaselineEntries])
    (by simp [runtimeBaseline, runtimeBaselineAux, getImplementationSlot])

theorem getIsOssified_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyGetIsOssifiedCalldata) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre getIsOssified out ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.getStor entry = Devm.getStor bodyPre := by
  exact endpoint_body_of_program (slot := getIsOssifiedSlot)
    (endpoint := getIsOssified) hprog hentryStack hvalue
    (selector_of_proxyGetIsOssifiedCalldata hdata)
    (by simp [runtimeBaselineEntries])
    (by simp [runtimeBaseline, runtimeBaselineAux, getIsOssifiedSlot])

theorem ossify_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyOssifyCalldata) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre ossify out ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.getStor entry = Devm.getStor bodyPre := by
  exact endpoint_body_of_program (slot := ossifySlot) (endpoint := ossify)
    hprog hentryStack hvalue
    (selector_of_proxyOssifyCalldata hdata)
    (by simp [runtimeBaselineEntries])
    (by simp [runtimeBaseline, runtimeBaselineAux, ossifySlot])

theorem changeAdmin_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre changeAdmin out ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.getStor entry = Devm.getStor bodyPre := by
  exact endpoint_body_of_program (slot := changeAdminSlot)
    (endpoint := changeAdmin) hprog hentryStack hvalue
    (selector_of_proxyChangeAdminCalldata hdata)
    (by simp [runtimeBaselineEntries])
    (by simp [runtimeBaseline, runtimeBaselineAux, changeAdminSlot])

theorem upgradeTo_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre upgradeTo out ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.getStor entry = Devm.getStor bodyPre := by
  exact endpoint_body_of_program (slot := upgradeToSlot) (endpoint := upgradeTo)
    hprog hentryStack hvalue
    (selector_of_proxyUpgradeToCalldata hdata)
    (by simp [runtimeBaselineEntries])
    (by simp [runtimeBaseline, runtimeBaselineAux, upgradeToSlot])

theorem upgradeToAndCall_body_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre upgradeToAndCall out ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.getStor entry = Devm.getStor bodyPre := by
  exact endpoint_body_of_program (slot := upgradeToAndCallSlot)
    (endpoint := upgradeToAndCall) hprog hentryStack hvalue
    (selector_of_proxyUpgradeToAndCallCalldata hdata)
    (by simp [runtimeBaselineEntries])
    (by simp [runtimeBaseline, runtimeBaselineAux, upgradeToAndCallSlot])

/-! ## Program-to-authorization consumers -/

theorem storedAdminWord_eq_of_getStor_eq
    {left right : Devm} {owner : Adr}
    (h : Devm.getStor left = Devm.getStor right) :
    storedAdminWord left owner = storedAdminWord right owner := by
  unfold storedAdminWord canonicalAddressWord
  change (~~~addressMask) &&& (Devm.getStor left owner).get adminSlotLit =
    (~~~addressMask) &&& (Devm.getStor right owner).get adminSlotLit
  rw [h]

theorem storedImplementationWord_eq_of_getStor_eq
    {left right : Devm} {owner : Adr}
    (h : Devm.getStor left = Devm.getStor right) :
    storedImplementationWord left owner =
      storedImplementationWord right owner := by
  unfold storedImplementationWord canonicalAddressWord
  change (~~~addressMask) &&&
      (Devm.getStor left owner).get implementationSlotLit =
    (~~~addressMask) &&&
      (Devm.getStor right owner).get implementationSlotLit
  rw [h]

/-! ## Exact successful getters from the compiled program -/

theorem getAdmin_exact_of_program
    {sevm : Sevm} {entry post : Devm}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = [])
    (hdata : sevm.data = proxyGetAdminCalldata) :
    sevm.value = 0 ∧
      ReturnsWord (storedAdminWord entry sevm.currentTarget) post ∧
      Devm.getStor entry = Devm.getStor post := by
  have hselector := selector_of_proxyGetAdminCalldata hdata
  have hmember :
      (proxyGetAdminSelector, nonpayable (.call getAdminSlot)) ∈
        runtimeBaselineEntries := by
    simp [runtimeBaselineEntries]
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, _⟩ :=
    runtime_selected_body_of_prog_run_empty_frame hprog hentryStack hselector
      hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  have hvalue : sevm.value = 0 :=
    (Func.RunCompiledTo.nonpayable_body_of_ok pDispatch dispatchRun).1
  obtain ⟨bodyPre, bodyRun, pBody, bodyStor⟩ :=
    getAdmin_body_of_program hprog hentryStack hvalue hdata
  have hword := getAdmin_successful_body_returns pBody bodyRun
  have hstored := storedAdminWord_eq_of_getStor_eq bodyStor
    (owner := sevm.currentTarget)
  rw [← hstored] at hword
  have bodySource : Func.Run
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm bodyPre getAdmin post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok bodyRun)
  have bodyPreserves : Devm.getStor bodyPre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      rw [getAdmin_control_shape]
      func_inv) bodySource
  exact ⟨hvalue, hword, bodyStor.trans bodyPreserves⟩

theorem getImplementation_exact_of_program
    {sevm : Sevm} {entry post : Devm}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = [])
    (hdata : sevm.data = proxyGetImplementationCalldata) :
    sevm.value = 0 ∧
      ReturnsWord
        (storedImplementationWord entry sevm.currentTarget) post ∧
      Devm.getStor entry = Devm.getStor post := by
  have hselector := selector_of_proxyGetImplementationCalldata hdata
  have hmember :
      (proxyGetImplementationSelector,
        nonpayable (.call getImplementationSlot)) ∈
        runtimeBaselineEntries := by
    simp [runtimeBaselineEntries]
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, _⟩ :=
    runtime_selected_body_of_prog_run_empty_frame hprog hentryStack hselector
      hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  have hvalue : sevm.value = 0 :=
    (Func.RunCompiledTo.nonpayable_body_of_ok pDispatch dispatchRun).1
  obtain ⟨bodyPre, bodyRun, pBody, bodyStor⟩ :=
    getImplementation_body_of_program hprog hentryStack hvalue hdata
  have hword := getImplementation_successful_body_returns pBody bodyRun
  have hstored := storedImplementationWord_eq_of_getStor_eq bodyStor
    (owner := sevm.currentTarget)
  rw [← hstored] at hword
  have bodySource : Func.Run
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm bodyPre getImplementation post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok bodyRun)
  have bodyPreserves : Devm.getStor bodyPre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      rw [getImplementation_control_shape]
      func_inv) bodySource
  exact ⟨hvalue, hword, bodyStor.trans bodyPreserves⟩

theorem getIsOssified_exact_of_program
    {sevm : Sevm} {entry post : Devm}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = [])
    (hdata : sevm.data = proxyGetIsOssifiedCalldata) :
    sevm.value = 0 ∧
      ReturnsWord (storedAdminWord entry sevm.currentTarget =? 0) post ∧
      Devm.getStor entry = Devm.getStor post := by
  have hselector := selector_of_proxyGetIsOssifiedCalldata hdata
  have hmember :
      (proxyGetIsOssifiedSelector, nonpayable (.call getIsOssifiedSlot)) ∈
        runtimeBaselineEntries := by
    simp [runtimeBaselineEntries]
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, _⟩ :=
    runtime_selected_body_of_prog_run_empty_frame hprog hentryStack hselector
      hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  have hvalue : sevm.value = 0 :=
    (Func.RunCompiledTo.nonpayable_body_of_ok pDispatch dispatchRun).1
  obtain ⟨bodyPre, bodyRun, pBody, bodyStor⟩ :=
    getIsOssified_body_of_program hprog hentryStack hvalue hdata
  have hword := getIsOssified_successful_body_returns pBody bodyRun
  have hstored := storedAdminWord_eq_of_getStor_eq bodyStor
    (owner := sevm.currentTarget)
  rw [← hstored] at hword
  have bodySource : Func.Run
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm bodyPre getIsOssified post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok bodyRun)
  have bodyPreserves : Devm.getStor bodyPre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      rw [getIsOssified_control_shape]
      func_inv) bodySource
  exact ⟨hvalue, hword, bodyStor.trans bodyPreserves⟩

theorem getIsOssified_true_of_program
    {sevm : Sevm} {entry post : Devm}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = [])
    (hdata : sevm.data = proxyGetIsOssifiedCalldata)
    (adminZero : storedAdminWord entry sevm.currentTarget = 0) :
    post.output = proxyIsOssifiedReturnData true := by
  have exactResult :=
    getIsOssified_exact_of_program hprog hentryStack hdata
  simpa [ReturnsWord, proxyIsOssifiedReturnData, adminZero, B256.eqCheck]
    using exactResult.2.1

theorem changeAdmin_activeAdminRoute_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin) :
    ∃ authPre,
      ActiveAdminRoute
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm authPre changeAdminMutation [] out ∧
      Devm.getStor entry = Devm.getStor authPre := by
  obtain ⟨decodePre, decodeRun, pDecode, decodeStor⟩ :=
    changeAdmin_body_of_program hprog hentryStack hvalue hdata
  rw [changeAdmin_control_shape] at decodeRun
  have hlen : sevm.data.length = 36 := by
    rw [hdata]
    exact proxyChangeAdminCalldata_length newAdmin
  have hsize : B256.ltCheck sevm.data.length.toB256 (36 : B256) = 0 := by
    rw [hlen]
    decide
  have hvalid : ValidAdr (Sevm.argWord sevm 0) := by
    rw [proxyChangeAdminCalldata_arg0 hdata]
    exact validAdr_toB256 newAdmin
  obtain ⟨authPre, authRun, pAuth, authStor⟩ :=
    decodeAddressArg0Control_body pDecode hsize hvalid decodeRun
  exact ⟨authPre, activeAdminControl_route pAuth authRun,
    decodeStor.trans authStor⟩

theorem upgradeTo_activeAdminRoute_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation) :
    ∃ authPre,
      ActiveAdminRoute
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm authPre (upgradeImplementationControl Func.stop) [] out ∧
      Devm.getStor entry = Devm.getStor authPre := by
  obtain ⟨decodePre, decodeRun, pDecode, decodeStor⟩ :=
    upgradeTo_body_of_program hprog hentryStack hvalue hdata
  rw [upgradeTo_control_shape] at decodeRun
  have hlen : sevm.data.length = 36 := by
    rw [hdata]
    exact proxyUpgradeToCalldata_length newImplementation
  have hsize : B256.ltCheck sevm.data.length.toB256 (36 : B256) = 0 := by
    rw [hlen]
    decide
  have hvalid : ValidAdr (Sevm.argWord sevm 0) := by
    rw [proxyUpgradeToCalldata_arg0 hdata]
    exact validAdr_toB256 newImplementation
  obtain ⟨authPre, authRun, pAuth, authStor⟩ :=
    decodeAddressArg0Control_body pDecode hsize hvalid decodeRun
  exact ⟨authPre, activeAdminControl_route pAuth authRun,
    decodeStor.trans authStor⟩

/-- A live caller mismatch reaches `NotAdmin` from the exact public
`changeAdmin` program route. -/
theorem changeAdmin_unauthorized_route
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminNeCaller : storedAdminWord entry sevm.currentTarget ≠
      sevm.caller.toB256) :
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call notAdminErrorSlot) out := by
  obtain ⟨authPre, route, authStor⟩ :=
    changeAdmin_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have hadmin := storedAdminWord_eq_of_getStor_eq authStor
    (owner := sevm.currentTarget)
  apply ActiveAdminRoute.notAdmin_of_live_mismatch
    (route := route)
  · rwa [← hadmin]
  · rwa [← hadmin]

theorem changeAdmin_ossified_precedence
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin)
    (adminZero : storedAdminWord entry sevm.currentTarget = 0) :
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call proxyIsOssifiedErrorSlot) out := by
  obtain ⟨authPre, route, authStor⟩ :=
    changeAdmin_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have hadmin := storedAdminWord_eq_of_getStor_eq authStor
    (owner := sevm.currentTarget)
  apply ActiveAdminRoute.ossified_of_admin_zero (route := route)
  rwa [← hadmin]

/-- An ossified proxy reaches `ProxyIsOssified` before caller comparison on
`upgradeTo`; in particular this theorem admits a mismatching caller without
using that mismatch. -/
theorem upgradeTo_ossified_precedence
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation)
    (adminZero : storedAdminWord entry sevm.currentTarget = 0) :
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call proxyIsOssifiedErrorSlot) out := by
  obtain ⟨authPre, route, authStor⟩ :=
    upgradeTo_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have hadmin := storedAdminWord_eq_of_getStor_eq authStor
    (owner := sevm.currentTarget)
  apply ActiveAdminRoute.ossified_of_admin_zero (route := route)
  rwa [← hadmin]

/-- A live authorized `changeAdmin` reaches the exact mutation schedule.  If
the new admin equals the current admin, the same conclusion holds: there is no
same-value suppression guard before the event/write schedule. -/
theorem changeAdmin_authorized_reaches_mutation
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ mutationPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm mutationPre changeAdminMutation out ∧
      ([] : Stack) <<+ mutationPre.stack := by
  obtain ⟨authPre, route, authStor⟩ :=
    changeAdmin_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have hadmin := storedAdminWord_eq_of_getStor_eq authStor
    (owner := sevm.currentTarget)
  apply ActiveAdminRoute.authorized_of_live_caller (route := route)
  · rwa [← hadmin]
  · rwa [← hadmin]

theorem changeAdmin_same_value_reaches_mutation
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256)
    (sameValue : newAdmin.toB256 =
      storedAdminWord entry sevm.currentTarget) :
    ∃ mutationPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm mutationPre changeAdminMutation out ∧
      Sevm.argWord sevm 0 = storedAdminWord entry sevm.currentTarget := by
  obtain ⟨mutationPre, mutationRun, _⟩ :=
    changeAdmin_authorized_reaches_mutation hprog hentryStack hvalue hdata
      adminNonzero adminEqCaller
  exact ⟨mutationPre, mutationRun,
    (proxyChangeAdminCalldata_arg0 hdata).trans sameValue⟩

/-- A live authorized `upgradeTo` reaches the exact implementation code check.
The schedule has no old/new comparison, so same-value implementations are
checked, written, and announced along the same route as different values. -/
theorem upgradeTo_authorized_reaches_code_check
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ checkPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm checkPre (upgradeImplementationControl Func.stop) out ∧
      ([] : Stack) <<+ checkPre.stack := by
  obtain ⟨authPre, route, authStor⟩ :=
    upgradeTo_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have hadmin := storedAdminWord_eq_of_getStor_eq authStor
    (owner := sevm.currentTarget)
  apply ActiveAdminRoute.authorized_of_live_caller (route := route)
  · rwa [← hadmin]
  · rwa [← hadmin]

theorem upgradeTo_same_value_reaches_code_check
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256)
    (sameValue : newImplementation.toB256 =
      storedImplementationWord entry sevm.currentTarget) :
    ∃ checkPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm checkPre (upgradeImplementationControl Func.stop) out ∧
      Sevm.argWord sevm 0 =
        storedImplementationWord entry sevm.currentTarget := by
  obtain ⟨checkPre, checkRun, _⟩ :=
    upgradeTo_authorized_reaches_code_check hprog hentryStack hvalue hdata
      adminNonzero adminEqCaller
  exact ⟨checkPre, checkRun,
    (proxyUpgradeToCalldata_arg0 hdata).trans sameValue⟩

/-- The public ossify entry reaches the exact authorization classification
directly from its compiled-program run. -/
theorem ossify_activeAdminRoute_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyOssifyCalldata) :
    ∃ authPre,
      ActiveAdminRoute
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm authPre ossifyMutation [] out ∧
      Devm.getStor entry = Devm.getStor authPre := by
  obtain ⟨authPre, authRun, pAuth, authStor⟩ :=
    ossify_body_of_program hprog hentryStack hvalue hdata
  rw [ossify_control_shape] at authRun
  exact ⟨authPre, activeAdminControl_route pAuth authRun, authStor⟩

theorem ossify_ossified_precedence
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyOssifyCalldata)
    (adminZero : storedAdminWord entry sevm.currentTarget = 0) :
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call proxyIsOssifiedErrorSlot) out := by
  obtain ⟨authPre, route, authStor⟩ :=
    ossify_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have hadmin := storedAdminWord_eq_of_getStor_eq authStor
    (owner := sevm.currentTarget)
  apply ActiveAdminRoute.ossified_of_admin_zero (route := route)
  rwa [← hadmin]

theorem ossify_authorized_reaches_mutation
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyOssifyCalldata)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ mutationPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm mutationPre ossifyMutation out ∧
      ([] : Stack) <<+ mutationPre.stack := by
  obtain ⟨authPre, route, authStor⟩ :=
    ossify_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have hadmin := storedAdminWord_eq_of_getStor_eq authStor
    (owner := sevm.currentTarget)
  apply ActiveAdminRoute.authorized_of_live_caller (route := route)
  · rwa [← hadmin]
  · rwa [← hadmin]

/-! ## Named-call nonpayable precedence -/

/-- Every one of the seven named selectors rejects nonzero value with empty
revert data at the dispatcher wrapper, before its auxiliary call (and hence
before decoding, authorization, code checks, storage writes, or logs). -/
theorem named_call_with_value_reverts_before_endpoint
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector : B256} {slot : Nat}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value ≠ 0)
    (hselector : Sevm.selector sevm = selector)
    (hmember : (selector, nonpayable (.call slot)) ∈
      runtimeBaselineEntries) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, _⟩ :=
    runtime_selected_body_of_prog_run_empty_frame hprog hentryStack hselector
      hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  exact Func.RunCompiledTo.nonpayable_revert_of_value_nonzero hvalue
    pDispatch dispatchRun

theorem getAdmin_with_value_reverts
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value ≠ 0)
    (hdata : sevm.data = proxyGetAdminCalldata) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  exact named_call_with_value_reverts_before_endpoint (slot := getAdminSlot)
    hprog hentryStack hvalue
    (selector_of_proxyGetAdminCalldata hdata)
    (by simp [runtimeBaselineEntries])

theorem getImplementation_with_value_reverts
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value ≠ 0)
    (hdata : sevm.data = proxyGetImplementationCalldata) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  exact named_call_with_value_reverts_before_endpoint
    (slot := getImplementationSlot) hprog hentryStack hvalue
    (selector_of_proxyGetImplementationCalldata hdata)
    (by simp [runtimeBaselineEntries])

theorem getIsOssified_with_value_reverts
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value ≠ 0)
    (hdata : sevm.data = proxyGetIsOssifiedCalldata) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  exact named_call_with_value_reverts_before_endpoint
    (slot := getIsOssifiedSlot) hprog hentryStack hvalue
    (selector_of_proxyGetIsOssifiedCalldata hdata)
    (by simp [runtimeBaselineEntries])

theorem changeAdmin_with_value_reverts
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value ≠ 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  exact named_call_with_value_reverts_before_endpoint (slot := changeAdminSlot)
    hprog hentryStack hvalue
    (selector_of_proxyChangeAdminCalldata hdata)
    (by simp [runtimeBaselineEntries])

theorem upgradeTo_with_value_reverts
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value ≠ 0)
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  exact named_call_with_value_reverts_before_endpoint (slot := upgradeToSlot)
    hprog hentryStack hvalue
    (selector_of_proxyUpgradeToCalldata hdata)
    (by simp [runtimeBaselineEntries])

theorem upgradeToAndCall_with_value_reverts
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value ≠ 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  exact named_call_with_value_reverts_before_endpoint
    (slot := upgradeToAndCallSlot) hprog hentryStack hvalue
    (selector_of_proxyUpgradeToAndCallCalldata hdata)
    (by simp [runtimeBaselineEntries])

theorem ossify_with_value_reverts
    {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value ≠ 0)
    (hdata : sevm.data = proxyOssifyCalldata) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  exact named_call_with_value_reverts_before_endpoint (slot := ossifySlot)
    hprog hentryStack hvalue
    (selector_of_proxyOssifyCalldata hdata)
    (by simp [runtimeBaselineEntries])

end ProxyPair
end Blanc
