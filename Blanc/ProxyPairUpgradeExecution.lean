import Blanc.ProxyPairUpgradeRelation
import Blanc.ProxyPairOssifiableUpgradeToAndCall
import Blanc.ProxyPairOssifiableForwarding

/-!
# Exact proxy upgrade and post-upgrade executions

Closed Prague fixtures execute the exact compiled 2,188-byte OssifiableProxy
runtime and the exact goal-local implementation artifacts.  The primary route
performs a real nonempty setup delegatecall.  The identity routes execute the
public proxy entries without changing application storage.
-/

namespace Blanc.ProxyPair.Upgrade

open Jaune
open scoped LogOutputHinv

/-! ## Exact installed world -/

def fixtureProxyStorage : Stor :=
  ((Stor.empty : Stor).set implementationSlotLit v1Implementation.toB256)
    |>.set adminSlotLit upgradeAdmin.toB256
    |>.set v1ValueSlot 42

def fixturePrestate : State :=
  let withV1 := State.set (.empty : State) v1Implementation
    { Acct.nil with code := v1Code }
  let withV2 := State.set withV1 v2Implementation
    { Acct.nil with code := v2Code }
  State.set withV2 upgradeProxy
    { Acct.nil with stor := fixtureProxyStorage, code := runtimeBaselineCode }

def fixtureBenv : Benv :=
  { (default : Benv) with
    state := fixturePrestate
    stat :=
      { (default : BenvStat) with
        rules := pragueRules
        origState := fixturePrestate } }

def upgradeMessage (data : Bytes) : Msg :=
  { (default : Msg) with
    benv := fixtureBenv
    caller := upgradeAdmin
    target := some upgradeProxy
    currentTarget := upgradeProxy
    gas := 5000000
    value := 0
    data := data
    codeAddress := some upgradeProxy
    code := runtimeBaselineCode
    depth := 1024
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := true }

def primaryMessage : Msg :=
  upgradeMessage (proxyUpgradeToAndCallCalldata v2Implementation
    initializeV2Calldata false)

def upgradeToMessage : Msg :=
  upgradeMessage (proxyUpgradeToCalldata v2Implementation)

def skippedEmptyMessage : Msg :=
  upgradeMessage (proxyUpgradeToAndCallCalldata v2Implementation [] false)

/-! ## Shared implementation bodies -/

theorem loadScalar_run_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {slot : B256} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (loadScalar slot) (.ok post)) :
    ReturnsWord (pre.getStorVal sevm.currentTarget slot) post ∧
      Devm.getStor pre = Devm.getStor post := by
  have source : Func.Run fs sevm pre (loadScalar slot) post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  unfold loadScalar at run
  obtain ⟨pushPost, qpush, run⟩ := runCompiledTo_next_inv run
  obtain ⟨loadPost, qload, run⟩ := runCompiledTo_next_inv run
  have pPush : slot :: tail <<+ pushPost.stack :=
    prefix_of_push (of_run_pushB256 (Ninst.Run.of_runCompiled qpush)) hp
  obtain ⟨loaded, pLoad, loadedEq⟩ :=
    prefix_of_sload (Ninst.Run.of_runCompiled qload) pPush
  have returned := returnsWord_of_storeReturn pLoad
    (Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run))
  have pushStor : Devm.getStor pre = Devm.getStor pushPost :=
    Ninst.Hinv.inv (f := Devm.getStor) (Ninst.Run.of_runCompiled qpush)
  have loadedFromPre :
      pushPost.getStorVal sevm.currentTarget slot =
        pre.getStorVal sevm.currentTarget slot := by
    change (Devm.getStor pushPost sevm.currentTarget).get slot =
      (Devm.getStor pre sevm.currentTarget).get slot
    rw [← congrFun pushStor sevm.currentTarget]
  have returned' :
      ReturnsWord (pre.getStorVal sevm.currentTarget slot) post := by
    rw [← loadedFromPre, ← loadedEq]
    exact returned.1
  have storage : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor
      (by unfold loadScalar; func_inv) source
  exact ⟨returned', storage⟩

theorem storeScalar_run_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {slot : B256} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (storeScalar slot) (.ok post)) :
    Devm.getStor post sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set slot
          (Sevm.argWord sevm 0) ∧
      post.output = pre.output := by
  have source : Func.Run fs sevm pre (storeScalar slot) post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  unfold storeScalar at run
  obtain ⟨argPost, argRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pushPost, qpush, run⟩ := runCompiledTo_next_inv run
  obtain ⟨storePost, qstore, stopRun⟩ := runCompiledTo_next_inv run
  have pArg : Sevm.argWord sevm 0 :: tail <<+ argPost.stack :=
    prefix_of_arg hp argRun
  have pPush : slot :: Sevm.argWord sevm 0 :: tail <<+
      pushPost.stack :=
    prefix_of_push (of_run_pushB256 (Ninst.Run.of_runCompiled qpush)) pArg
  have write := sstore_getStor_set (Ninst.Run.of_runCompiled qstore) pPush
  have postEq : post = storePost := Func.RunCompiledTo.stop_eq stopRun
  have prePushStor : Devm.getStor pre = Devm.getStor pushPost :=
    (Line.of_inv Devm.getStor (by line_inv) argRun).trans
      (Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled qpush))
  have storage : Devm.getStor post sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set slot
        (Sevm.argWord sevm 0) := by
    rw [postEq, write, ← congrFun prePushStor sevm.currentTarget]
  have output : pre.output = post.output :=
    Func.of_inv Devm.output Devm.output
      (by unfold storeScalar; func_inv) source
  exact ⟨storage, output.symm⟩

/-- The successful nonpayable wrapper reaches its body without changing
storage or output.  This is the stronger frame needed to derive the scalar
witness effects from their compiled walks rather than storing those effects
in an execution certificate. -/
private theorem nonpayable_body_of_ok_frame
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (nonpayable body) (.ok post)) :
    sevm.value = 0 ∧
      ∃ bodyPre,
        Func.RunCompiledTo fs sevm bodyPre body (.ok post) ∧
        tail <<+ bodyPre.stack ∧
        Devm.DispatchFramePreserved pre bodyPre := by
  have valueZero : sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled
        (Func.RunCompiled.of_runCompiledTo_ok run))
  unfold nonpayable at run
  obtain ⟨afterValue, qvalue, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have rvalue := Ninst.Run.of_runCompiled qvalue
  have rzero := Ninst.Run.of_runCompiled qzero
  have valuePush := of_run_callvalue rvalue
  have pValue := prefix_of_push valuePush hp
  have pTest := prefix_of_iszero rzero pValue
  have pOne : (1 : B256) :: tail <<+ testPre.stack := by
    simpa [valueZero, B256.eqCheck] using pTest
  obtain ⟨bodyPre, _, -, hpop, bodyRun, pBody⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  have zeroDiff : ∃ x, Devm.DiffBurn [x] [x =? 0]
      afterValue testPre := by
    rcases of_run_reg rzero with ⟨_, zeroRun⟩
    simp only [Rinst.run, Rinst.runCore] at zeroRun
    exact Devm.diffBurn_of_applyUnary zeroRun
  obtain ⟨_, zeroBurn⟩ := zeroDiff
  have bodyFrame : Devm.DispatchFramePreserved pre bodyPre :=
    (dispatchFrame_of_pushBurn valuePush).trans
      ((dispatchFrame_of_diffBurn zeroBurn).trans
        (dispatchFrame_of_popBurnBy hpop))
  exact ⟨valueZero, bodyPre, bodyRun, pBody, bodyFrame⟩

/-- Open the exact public `upgradeToAndCall` entry while retaining the full
entry-to-endpoint frame.  The predecessor endpoint helper intentionally keeps
only storage; this stronger local form is needed to carry a concrete memory
image into the dynamic decoder without postulating a later route. -/
private theorem upgradeToAndCall_body_of_program_frame
    {sevm : Sevm} {entry post : Devm}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = []) (_hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall) :
    ∃ bodyPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm bodyPre upgradeToAndCall (.ok post) ∧
      ([] : Stack) <<+ bodyPre.stack ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, dispatchFrame⟩ :=
    runtime_selected_body_of_prog_run_empty_frame
      (body := nonpayable (.call upgradeToAndCallSlot)) hprog hentryStack
      (selector_of_proxyUpgradeToAndCallCalldata hdata)
      (by simp [runtimeBaselineEntries])
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  obtain ⟨_, callPre, callRun, pCall, callFrame⟩ :=
    nonpayable_body_of_ok_frame pDispatch dispatchRun
  obtain ⟨bodyPre, callBurn, bodyRun⟩ := runCompiledTo_call_inv
    (k := upgradeToAndCallSlot) (f := upgradeToAndCall)
    (by simp [runtimeBaseline, runtimeBaselineAux, upgradeToAndCallSlot])
    callRun
  have pBody : ([] : Stack) <<+ bodyPre.stack := by
    rw [← callBurn.stack]
    exact pCall
  exact ⟨bodyPre, bodyRun, pBody,
    dispatchFrame.trans
      (callFrame.trans (dispatchFrame_of_burnBy callBurn))⟩

/-- Open a selected nonpayable body in either exact scalar witness program,
retaining the complete entry-to-body storage equality. -/
private theorem witness_selected_body_of_program
    (entries : List (B256 × Func)) (prog : Prog)
    (hshape : prog =
      ⟨fsig +++ linearDispatchWith 0 entries, [Func.revert]⟩)
    {sevm : Sevm} {pre post : Devm} {selected : B256} {body : Func}
    (hprog : Prog.RunCompiledTo sevm pre prog (.ok post))
    (hstack : pre.stack = [])
    (hselector : Sevm.selector sevm = selected)
    (huniq : selectorUnique entries)
    (hmember : (selected, nonpayable body) ∈ entries) :
    ∃ bodyPre,
      Func.RunCompiledTo
          ((fsig +++ linearDispatchWith 0 entries) :: [Func.revert])
          sevm bodyPre body (.ok post) ∧
        ([] : Stack) <<+ bodyPre.stack ∧
        Devm.getStor pre = Devm.getStor bodyPre ∧
        pre.output = bodyPre.output := by
  subst prog
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo
    ((fsig +++ linearDispatchWith 0 entries) :: [Func.revert])
      sevm mid (fsig +++ linearDispatchWith 0 entries) (.ok post) at hmain
  obtain ⟨afterSig, hsig, hdispatch⟩ := runCompiledTo_prepend_inv hmain
  have hmidStack : mid.stack = [] := by
    rw [← hburn.stack]
    exact hstack
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
  have hafterSigStack : afterSig.stack = selected :: [] := by
    have hs := stack_of_diffBurn_two hshrDiff hshiftStack
    rw [← hselector]
    exact hs
  rcases dispatchBodyWitness_of_runCompiledTo huniq hmember
      hafterSigStack hdispatch with
    ⟨selectedPre, _, selectedRun, _, dispatchFrame⟩
  rcases nonpayable_body_of_ok_frame
      (tail := []) nil_pref selectedRun with
    ⟨_, bodyPre, bodyRun, bodyStack, selectedBodyFrame⟩
  have hsigStor : Devm.getStor mid = Devm.getStor afterSig :=
    (Ninst.Hinv.inv (f := Devm.getStor) qpush0).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) qload).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) qpush224).trans
          (Ninst.Hinv.inv (f := Devm.getStor) qshr)))
  have entrySelectedStor : Devm.getStor pre = Devm.getStor selectedPre :=
    (funext (getStor_eq_of_state_eq hburn.state)).trans
      (hsigStor.trans (funext (getStor_eq_of_state_eq dispatchFrame.state)))
  have hsigOutput : mid.output = afterSig.output :=
    (Ninst.Hinv.inv (f := Devm.output) qpush0).trans
      ((Ninst.Hinv.inv (f := Devm.output) qload).trans
        ((Ninst.Hinv.inv (f := Devm.output) qpush224).trans
          (Ninst.Hinv.inv (f := Devm.output) qshr)))
  have entrySelectedOutput : pre.output = selectedPre.output :=
    hburn.output.trans (hsigOutput.trans dispatchFrame.output)
  exact ⟨bodyPre, bodyRun, bodyStack,
    entrySelectedStor.trans
      (funext (getStor_eq_of_state_eq selectedBodyFrame.state)),
    entrySelectedOutput.trans selectedBodyFrame.output⟩

/-- Exact compiled v1 `value()` behavior over S1. -/
theorem v1_value_run_effect
    {sevm : Sevm} {pre post : Devm}
    (hprog : Prog.RunCompiledTo sevm pre v1Prog (.ok post))
    (hstack : pre.stack = []) (hdata : sevm.data = valueCalldata) :
    ReturnsWord (pre.getStorVal sevm.currentTarget v1ValueSlot) post ∧
      Devm.getStor pre = Devm.getStor post := by
  obtain ⟨bodyPre, bodyRun, bodyStack, entryBodyStor, _entryBodyOutput⟩ :=
    witness_selected_body_of_program v1Entries v1Prog rfl
      (selected := valueSelector) (body := loadScalar v1ValueSlot)
      hprog hstack
      (selector_of_valueCalldata hdata) v1Entries_selectorUnique
      (by simp [v1Entries])
  have effect := loadScalar_run_effect bodyStack bodyRun
  have wordEq : bodyPre.getStorVal sevm.currentTarget v1ValueSlot =
      pre.getStorVal sevm.currentTarget v1ValueSlot := by
    change (Devm.getStor bodyPre sevm.currentTarget).get v1ValueSlot =
      (Devm.getStor pre sevm.currentTarget).get v1ValueSlot
    rw [← congrFun entryBodyStor sevm.currentTarget]
  exact ⟨by simpa [wordEq] using effect.1,
    entryBodyStor.trans effect.2⟩

/-- Exact compiled v2 `value()` behavior over S2. -/
theorem v2_value_run_effect
    {sevm : Sevm} {pre post : Devm}
    (hprog : Prog.RunCompiledTo sevm pre v2Prog (.ok post))
    (hstack : pre.stack = []) (hdata : sevm.data = valueCalldata) :
    ReturnsWord (pre.getStorVal sevm.currentTarget v2ValueSlot) post ∧
      Devm.getStor pre = Devm.getStor post := by
  obtain ⟨bodyPre, bodyRun, bodyStack, entryBodyStor, _entryBodyOutput⟩ :=
    witness_selected_body_of_program v2Entries v2Prog rfl
      (selected := valueSelector) (body := loadScalar v2ValueSlot)
      hprog hstack
      (selector_of_valueCalldata hdata) v2Entries_selectorUnique
      (by simp [v2Entries])
  have effect := loadScalar_run_effect bodyStack bodyRun
  have wordEq : bodyPre.getStorVal sevm.currentTarget v2ValueSlot =
      pre.getStorVal sevm.currentTarget v2ValueSlot := by
    change (Devm.getStor bodyPre sevm.currentTarget).get v2ValueSlot =
      (Devm.getStor pre sevm.currentTarget).get v2ValueSlot
    rw [← congrFun entryBodyStor sevm.currentTarget]
  exact ⟨by simpa [wordEq] using effect.1,
    entryBodyStor.trans effect.2⟩

/-- Exact compiled v1 `setValue(uint256)` behavior over S1. -/
theorem v1_setValue_run_effect
    {sevm : Sevm} {pre post : Devm} {word : B256}
    (hprog : Prog.RunCompiledTo sevm pre v1Prog (.ok post))
    (hstack : pre.stack = [])
    (hdata : sevm.data = setValueCalldata word) :
    Devm.getStor post sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set v1ValueSlot word ∧
      post.output = pre.output := by
  obtain ⟨bodyPre, bodyRun, bodyStack, entryBodyStor,
      entryBodyOutput⟩ :=
    witness_selected_body_of_program v1Entries v1Prog rfl
      (selected := setValueSelector) (body := storeScalar v1ValueSlot)
      hprog hstack
      (selector_of_setValueCalldata hdata) v1Entries_selectorUnique
      (by simp [v1Entries])
  have effect := storeScalar_run_effect bodyStack bodyRun
  constructor
  · rw [effect.1, setValueCalldata_arg0 hdata,
      ← congrFun entryBodyStor sevm.currentTarget]
  · exact effect.2.trans entryBodyOutput.symm

/-- Exact compiled v2 `setValue(uint256)` behavior over S2.  The write does
not read or branch on the marker. -/
theorem v2_setValue_run_effect
    {sevm : Sevm} {pre post : Devm} {word : B256}
    (hprog : Prog.RunCompiledTo sevm pre v2Prog (.ok post))
    (hstack : pre.stack = [])
    (hdata : sevm.data = setValueCalldata word) :
    Devm.getStor post sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set v2ValueSlot word ∧
      post.output = pre.output := by
  obtain ⟨bodyPre, bodyRun, bodyStack, entryBodyStor,
      entryBodyOutput⟩ :=
    witness_selected_body_of_program v2Entries v2Prog rfl
      (selected := setValueSelector) (body := storeScalar v2ValueSlot)
      hprog hstack
      (selector_of_setValueCalldata hdata) v2Entries_selectorUnique
      (by simp [v2Entries])
  have effect := storeScalar_run_effect bodyStack bodyRun
  constructor
  · rw [effect.1, setValueCalldata_arg0 hdata,
      ← congrFun entryBodyStor sevm.currentTarget]
  · exact effect.2.trans entryBodyOutput.symm

/-! ## Exact initializer effect -/

/-- A successful walk of the selected initializer derives both writes from
the instruction semantics.  The conclusion is the complete proxy-owned
storage map, not a postcondition supplied by the caller. -/
theorem initializeV2Body_storage_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre initializeV2Body (.ok post)) :
    Devm.getStor post sevm.currentTarget =
      ((Devm.getStor pre sevm.currentTarget).set v2ValueSlot
        (Devm.getStorVal pre sevm.currentTarget v1ValueSlot)).set
          migrationMarkerSlot migrationMarkerValue ∧
      post.logs = pre.logs := by
  have source : Func.Run fs sevm pre initializeV2Body post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  unfold initializeV2Body at run
  obtain ⟨d1, q1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d3, q3, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d4, q4, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d5, q5, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d6, q6, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d7, q7, stopRun⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  have r7 := Ninst.Run.of_runCompiled q7
  have p1 : v1ValueSlot :: tail <<+ d1.stack :=
    prefix_of_push (of_run_pushB256 r1) hp
  obtain ⟨loaded, p2, loadedEq⟩ := prefix_of_sload r2 p1
  have p3 : v2ValueSlot :: loaded :: tail <<+ d3.stack :=
    prefix_of_push (of_run_pushB256 r3) p2
  have p4 : tail <<+ d4.stack := prefix_of_sstore r4 p3
  have p5 : migrationMarkerValue :: tail <<+ d5.stack :=
    prefix_of_push (of_run_pushB256 r5) p4
  have p6 : migrationMarkerSlot :: migrationMarkerValue :: tail <<+
      d6.stack := prefix_of_push (of_run_pushB256 r6) p5
  have firstWrite := sstore_getStor_set r4 p3
  have secondWrite := sstore_getStor_set r7 p6
  have postEq := Func.RunCompiledTo.stop_eq stopRun
  have e1 := Ninst.Hinv.inv (f := Devm.getStor) r1
  have e2 := Ninst.Hinv.inv (f := Devm.getStor) r2
  have e3 := Ninst.Hinv.inv (f := Devm.getStor) r3
  have e5 := Ninst.Hinv.inv (f := Devm.getStor) r5
  have e6 := Ninst.Hinv.inv (f := Devm.getStor) r6
  have loadedFromPre : Devm.getStorVal d1 sevm.currentTarget v1ValueSlot =
      Devm.getStorVal pre sevm.currentTarget v1ValueSlot := by
    change (Devm.getStor d1 sevm.currentTarget).get v1ValueSlot =
      (Devm.getStor pre sevm.currentTarget).get v1ValueSlot
    rw [← congrFun e1 sevm.currentTarget]
  constructor
  · rw [postEq, secondWrite, ← e6, ← e5, firstWrite, ← e3, ← e2, ← e1,
      loadedEq, loadedFromPre]
  · exact (Func.of_inv Devm.logs Devm.logs
      (by unfold initializeV2Body; func_inv) source).symm

/-- Selecting `initializeV2()` in the exact compiled v2 artifact reaches the
initializer body and therefore derives its two-write storage effect. -/
theorem v2_initializer_run_storage_effect
    {sevm : Sevm} {pre post : Devm}
    (hprog : Prog.RunCompiledTo sevm pre v2Prog (.ok post))
    (hstack : pre.stack = [])
    (hselector : Sevm.selector sevm = initializeV2Selector) :
    Devm.getStor post sevm.currentTarget =
      ((Devm.getStor pre sevm.currentTarget).set v2ValueSlot
        (Devm.getStorVal pre sevm.currentTarget v1ValueSlot)).set
          migrationMarkerSlot migrationMarkerValue ∧
      post.logs = pre.logs := by
  obtain ⟨mid, hburn, hmain⟩ := hprog
  change Func.RunCompiledTo (v2Prog.main :: v2Prog.aux) sevm mid
    (fsig +++ linearDispatchWith 0 v2Entries) (.ok post) at hmain
  obtain ⟨afterSig, hsig, hdispatch⟩ := runCompiledTo_prepend_inv hmain
  have hmidStack : mid.stack = [] := by
    rw [← hburn.stack]
    exact hstack
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
  have hafterSigStack : afterSig.stack = initializeV2Selector :: [] := by
    have hs := stack_of_diffBurn_two hshrDiff hshiftStack
    rw [← hselector]
    exact hs
  have huniq : selectorUnique v2Entries := by
    simp [selectorUnique, v2Entries, valueSelector, setValueSelector,
      initializeV2Selector, migrationMarkerSelector]
    repeat' apply And.intro
    all_goals decide +kernel
  have selected := dispatchBodyWitness_of_runCompiledTo
    huniq
    (show (initializeV2Selector, nonpayable initializeV2Body) ∈ v2Entries by
      simp [v2Entries])
    hafterSigStack hdispatch
  rcases selected with
    ⟨selectedPre, _, selectedRun, selectedStack, dispatchFrame⟩
  rcases nonpayable_body_of_ok_frame
      (tail := []) nil_pref selectedRun with
    ⟨_, bodyPre, bodyRun, bodyStack, selectedBodyFrame⟩
  have effect := initializeV2Body_storage_effect bodyStack bodyRun
  have hsigStor : Devm.getStor mid = Devm.getStor afterSig :=
    (Ninst.Hinv.inv (f := Devm.getStor) qpush0).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) qload).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) qpush224).trans
          (Ninst.Hinv.inv (f := Devm.getStor) qshr)))
  have entrySelectedStor : Devm.getStor pre = Devm.getStor selectedPre :=
    (funext (getStor_eq_of_state_eq hburn.state)).trans
      (hsigStor.trans (funext (getStor_eq_of_state_eq dispatchFrame.state)))
  have entryBodyStor : Devm.getStor pre = Devm.getStor bodyPre :=
    entrySelectedStor.trans
      (funext (getStor_eq_of_state_eq selectedBodyFrame.state))
  have hsigLogs : mid.logs = afterSig.logs :=
    (Ninst.Hinv.inv (f := Devm.logs) qpush0).trans
      ((Ninst.Hinv.inv (f := Devm.logs) qload).trans
        ((Ninst.Hinv.inv (f := Devm.logs) qpush224).trans
          (Ninst.Hinv.inv (f := Devm.logs) qshr)))
  have entryBodyLogs : pre.logs = bodyPre.logs :=
    hburn.logs.trans
      (hsigLogs.trans
        (dispatchFrame.logs.trans selectedBodyFrame.logs))
  constructor
  · rw [effect.1, ← congrFun entryBodyStor sevm.currentTarget]
    change
      ((Devm.getStor pre sevm.currentTarget).set v2ValueSlot
        ((Devm.getStor bodyPre sevm.currentTarget).get v1ValueSlot)).set
          migrationMarkerSlot migrationMarkerValue = _
    rw [← congrFun entryBodyStor sevm.currentTarget]
    rfl
  · exact effect.2.trans entryBodyLogs.symm

/-- A successful outer setup tail can only follow a clean delegated child;
the failed-child branch necessarily reverts or halts.  The settled child state
is therefore the exact state returned by the proxy frame. -/
theorem upgradeToAndCallDelegateTail_success_state
    {sevm : Sevm} {callPre callPost child post : Devm}
    {spawn : DelegatecallSpawnDescriptor sevm callPre}
    (settled : DelegatecallSettledBoundary spawn child callPost)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm callPost upgradeToAndCallDelegateTail (.ok post)) :
    child.error.isSome = false ∧ post.state = child.state ∧
      post.logs = spawn.parent.logs ++ child.logs := by
  rcases settled with
    ⟨_, _, returnData, stack, callState, _, callLogs⟩
  unfold upgradeToAndCallDelegateTail at run
  cases status : child.error.isSome with
  | false =>
      have pOne : (1 : B256) :: spawn.parent.stack <<+ callPost.stack :=
        ⟨[], by simpa [Split, status] using stack⟩
      obtain ⟨stopPre, _, _, branchPop, stopRun, _⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pOne run
      refine ⟨rfl, ?_, ?_⟩
      · rw [Func.RunCompiledTo.stop_eq stopRun]
        exact branchPop.state.symm.trans callState
      · rw [Func.RunCompiledTo.stop_eq stopRun]
        exact branchPop.logs.symm.trans (by simpa [status] using callLogs)
  | true =>
      have pZero : (0 : B256) :: spawn.parent.stack <<+ callPost.stack :=
        ⟨[], by simpa [Split, status] using stack⟩
      obtain ⟨failedPre, failedPop, failedRun, _⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pZero run
      obtain ⟨sizePost, sizeRun, payloadBranch⟩ :=
        runCompiledTo_next_inv failedRun
      have sizePush := of_run_returndatasize_val
        (Ninst.Run.of_runCompiled sizeRun)
      have failedReturnData : failedPre.returnData = child.output :=
        failedPop.returnData.symm.trans returnData
      by_cases lengthWordZero : Nat.toB256 child.output.length = 0
      · have pLengthZero : (0 : B256) :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData,
              lengthWordZero] using sizePush.stack⟩
        obtain ⟨_, _, errorRun, _⟩ :=
          Func.RunCompiledTo.zero_branch_of_prefix pLengthZero payloadBranch
        have hget :
            (runtimeBaseline.main :: runtimeBaseline.aux)[
                emptyDelegatecallErrorSlot]? =
              some (Func.revertData emptyDelegatecallErrorData) := by
          simp [runtimeBaseline, runtimeBaselineAux,
            emptyDelegatecallErrorSlot, emptyDelegatecallError]
        exact (Func.RunCompiledTo.not_ok_call_revertData hget errorRun).elim
      · have pLength : Nat.toB256 child.output.length :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData] using sizePush.stack⟩
        obtain ⟨_, _, _, _, bubbleRun, _⟩ :=
          Func.RunCompiledTo.succ_branch_of_prefix
            lengthWordZero pLength payloadBranch
        rcases Func.runCompiledTo_revertReturnData_inv bubbleRun with
          outOfGas | ⟨revertPost, revertOutcome, _⟩
        · rcases outOfGas with ⟨_, impossible⟩
          cases impossible
        · cases revertOutcome

private theorem DelegatecallSpawnDescriptor.parent_state_eq_callPre
    {sevm : Sevm} {callPre : Devm}
    (spawn : DelegatecallSpawnDescriptor sevm callPre) :
    spawn.parent.state = callPre.state := by
  have delegationState := congrArg
    (fun result : Bool × Adr × ByteArray × Nat × Devm =>
      result.2.2.2.2.state) spawn.delegationEq
  change spawn.afterAccess.state = callPre.state
  rw [← delegationState]
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress
      ((addAccessedAddress
        (callPre.setMach
          ⟨spawn.stackTail, callPre.memory, callPre.gasLeft⟩)
        spawn.codeWord.toAdr).state.getCode spawn.codeWord.toAdr) <;> rfl

private theorem DelegatecallSpawnDescriptor.parent_logs_eq_callPre
    {sevm : Sevm} {callPre : Devm}
    (spawn : DelegatecallSpawnDescriptor sevm callPre) :
    spawn.parent.logs = callPre.logs := by
  have delegationLogs := congrArg
    (fun result : Bool × Adr × ByteArray × Nat × Devm =>
      result.2.2.2.2.logs) spawn.delegationEq
  change spawn.afterAccess.logs = callPre.logs
  rw [← delegationLogs]
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress
      ((addAccessedAddress
        (callPre.setMach
          ⟨spawn.stackTail, callPre.memory, callPre.gasLeft⟩)
        spawn.codeWord.toAdr).state.getCode spawn.codeWord.toAdr) <;> rfl

/-- Extract the primary commit and nonempty setup boundary from the one exact
outer compiled execution.  The caller supplies only entry facts and a
concrete memory image; the check state, commit state, setup state, event, and
delegate boundary are all consequences of that same walk. -/
private theorem primary_outer_boundary_of_program
    {sevm : Sevm} {entry post : Devm} {entryImage : Bytes}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata v2Implementation
      initializeV2Calldata false)
    (hauthorized : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256)
    (hliveAdmin : storedAdminWord entry sevm.currentTarget ≠ 0)
    (hrawCommit : addressSlotUpdateRaw entry sevm.currentTarget
      implementationSlotLit v2Implementation.toB256 =
        v2Implementation.toB256)
    (hentryMemoryWf : Mem.Wf entry.memory)
    (hentryMemoryReads : Mem.Reads entry.memory entryImage) :
    ∃ (checkPre afterPre delegatePre : Devm) (decodedImage : Bytes),
      Devm.getStor entry = Devm.getStor checkPre ∧
      entry.logs = checkPre.logs ∧
      Devm.getStor afterPre sevm.currentTarget =
        (Devm.getStor checkPre sevm.currentTarget).set
          implementationSlotLit v2Implementation.toB256 ∧
      afterPre.logs = checkPre.logs ++
        [rawUpgradedLog sevm.currentTarget v2Implementation.toB256] ∧
      afterPre.state = delegatePre.state ∧
      afterPre.logs = delegatePre.logs ∧
      UpgradeToAndCallDelegateBoundary
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm delegatePre [] decodedImage v2Implementation
          initializeV2Calldata false (.ok post) := by
  obtain ⟨bodyPre, bodyRun, pBody, entryBodyFrame⟩ :=
    upgradeToAndCall_body_of_program_frame hprog hentryStack hvalue hdata
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryBodyFrame.memory]
    exact hentryMemoryWf
  have bodyReads : Mem.Reads bodyPre.memory entryImage := by
    rw [← entryBodyFrame.memory]
    exact hentryMemoryReads
  rw [upgradeToAndCall_control_shape] at bodyRun
  obtain ⟨authPre, authRun, pAuth, authWf, authReads, bodyAuthState,
      bodyAuthLogs⟩ :=
    decodeUpgradeToAndCallControl_boundary pBody bodyWf bodyReads hdata
      (by decide +kernel) (by decide +kernel) bodyRun
  have entryAuthStor : Devm.getStor entry = Devm.getStor authPre :=
    (funext (getStor_eq_of_state_eq entryBodyFrame.state)).trans
      (funext (getStor_eq_of_state_eq bodyAuthState))
  have adminAtAuth : storedAdminWord entry sevm.currentTarget =
      storedAdminWord authPre sevm.currentTarget :=
    storedAdminWord_eq_of_getStor_eq entryAuthStor
  have authNonzero : storedAdminWord authPre sevm.currentTarget ≠ 0 := by
    intro zero
    exact hliveAdmin (adminAtAuth.trans zero)
  have authEqCaller : storedAdminWord authPre sevm.currentTarget =
      sevm.caller.toB256 := adminAtAuth.symm.trans hauthorized
  cases activeAdminControl_route pAuth authRun with
  | ossified _ adminZero _ _ _ _ _ =>
      exact (authNonzero adminZero).elim
  | unauthorized _ _ adminNeCaller _ _ _ _ _ =>
      exact (adminNeCaller authEqCaller).elim
  | authorized checkPre _ _ checkRun pCheck authCheckStor
      authCheckMemory authCheckLogs =>
      have checkWf : Mem.Wf checkPre.memory := by
        rw [← authCheckMemory]
        exact authWf
      have checkReads : Mem.Reads checkPre.memory
          (upgradeToAndCallDecodedImage entryImage v2Implementation
            initializeV2Calldata false) := by
        rw [← authCheckMemory]
        exact authReads
      have entryCheckStor : Devm.getStor entry = Devm.getStor checkPre :=
        entryAuthStor.trans authCheckStor
      have entryCheckLogs : entry.logs = checkPre.logs :=
        entryBodyFrame.logs.trans (bodyAuthLogs.trans authCheckLogs)
      have classified := upgradeToAndCall_authorized_outcome pCheck checkWf
        checkReads (by decide +kernel) checkRun
      cases classified with
      | noCode _ _ _ outcome =>
          rcases outcome with ⟨_, impossible, _, _, _⟩ |
            ⟨_, impossible, _, _, _, _⟩
          · cases impossible
          · cases impossible
      | committed _ committed =>
          rcases committed with
            ⟨afterPre, afterRun, pAfter, committedStor, committedLogs,
              _committedMemory, setupRoute⟩
          have arg0 : Sevm.argWord sevm 0 = v2Implementation.toB256 :=
            proxyUpgradeToAndCallCalldata_arg0 hdata
          have checkRawCommit : addressSlotUpdateRaw checkPre
              sevm.currentTarget implementationSlotLit
              (Sevm.argWord sevm 0) = v2Implementation.toB256 := by
            have rawWordEq : checkPre.getStorVal sevm.currentTarget
                implementationSlotLit =
                entry.getStorVal sevm.currentTarget
                  implementationSlotLit := by
              change (Devm.getStor checkPre sevm.currentTarget).get
                  implementationSlotLit =
                (Devm.getStor entry sevm.currentTarget).get
                  implementationSlotLit
              rw [← congrFun entryCheckStor sevm.currentTarget]
            unfold addressSlotUpdateRaw at hrawCommit ⊢
            rw [arg0, rawWordEq]
            exact hrawCommit
          have committedStor' : Devm.getStor afterPre sevm.currentTarget =
              (Devm.getStor checkPre sevm.currentTarget).set
                implementationSlotLit v2Implementation.toB256 := by
            rw [committedStor, checkRawCommit]
          have committedLogs' : afterPre.logs = checkPre.logs ++
              [rawUpgradedLog sevm.currentTarget
                v2Implementation.toB256] := by
            simpa [arg0] using committedLogs
          cases setupRoute with
          | nonempty _ delegatePre delegateRun pDelegate delegateWf
              delegateReads setupState setupLogs =>
              have boundary := upgradeToAndCallDelegateSetup_boundary
                pDelegate delegateWf delegateReads delegateRun
              exact ⟨checkPre, afterPre, delegatePre,
                upgradeToAndCallDecodedImage entryImage v2Implementation
                  initializeV2Calldata false,
                entryCheckStor, entryCheckLogs, committedStor',
                committedLogs', setupState, setupLogs, boundary⟩
          | forced setupEmpty _ _ _ _ _ _ _ _ =>
              exact (initializeV2Calldata_nonempty setupEmpty).elim
          | skipped setupEmpty _ _ _ _ _ _ _ _ =>
              exact (initializeV2Calldata_nonempty setupEmpty).elim

/-- Implementation-side evidence for every concrete constructor of the
execution-derived setup boundary.  Quantifying over the boundary's hidden
call states prevents a caller from supplying an unrelated second call walk;
the only retained conclusion is the actual descriptor, settled child, exact
v2 compiled walk, and installed code/data identities.  No migration
postcondition is a field. -/
def PrimaryChildExecution
    (sevm : Sevm) (post : Devm) : Prop :=
  ∀ (delegatePre : Devm) (decodedImage : Bytes) (gasWord : B256)
      (callPre callPost : Devm)
      (_callRun : Ninst.RunCompiled sevm callPre (.exec .delegatecall) callPost)
      (_tailRun : Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPost upgradeToAndCallDelegateTail (.ok post))
      (_stack :
        gasWord :: v2Implementation.toB256 ::
          upgradeToAndCallSetupMemoryBase ::
          Nat.toB256 initializeV2Calldata.length :: 0 :: 0 :: [] <<+
            callPre.stack)
      (_memoryWf : Mem.Wf callPre.memory)
      (_memoryReads : Mem.Reads callPre.memory decodedImage)
      (_state : delegatePre.state = callPre.state)
      (_logs : delegatePre.logs = callPre.logs),
    ∃ (spawn : DelegatecallSpawnDescriptor sevm callPre) (child : Devm),
      Ninst.RunCompiled sevm callPre (.exec .delegatecall) callPost ∧
      Func.RunCompiledTo (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPost upgradeToAndCallDelegateTail (.ok post) ∧
      spawn.codeWord = v2Implementation.toB256 ∧
      spawn.resolvedCodeAddress = v2Implementation ∧
      spawn.code = v2Code ∧
      spawn.child.data = initializeV2Calldata ∧
      DelegatecallSettledBoundary spawn child callPost ∧
      Prog.RunCompiledTo (initSevm spawn.child) (initDevm spawn.child)
        v2Prog (.ok child)

/-- The primary product theorem.  The proxy program remains an explicit
parameter.  One exact compiled outer walk determines the authorized commit,
nonempty setup boundary, `Upgraded` event, and the child call states.  The
implementation-side certificate supplies only the exact child spawned at that
boundary; all migration postconditions are derived from compiled runs. -/
theorem upgradeToAndCall_primary_realizes_migration
    (proxyProg : Prog) (hproxy : proxyProg = runtimeBaseline)
    {sevm : Sevm} {entry post : Devm} {entryImage : Bytes}
    (houter : Prog.RunCompiledTo sevm entry proxyProg (.ok post))
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (howner : sevm.currentTarget = upgradeProxy)
    (hcaller : sevm.caller = upgradeAdmin)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata v2Implementation
      initializeV2Calldata false)
    (hauthorized : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256)
    (hliveAdmin : storedAdminWord entry sevm.currentTarget ≠ 0)
    (hv1Installed : storedImplementationWord entry sevm.currentTarget =
      v1Implementation.toB256)
    (hv2Code : entry.getCode v2Implementation = v2Code)
    (hrawCommit : addressSlotUpdateRaw entry sevm.currentTarget
      implementationSlotLit v2Implementation.toB256 =
        v2Implementation.toB256)
    (hentryMemoryWf : Mem.Wf entry.memory)
    (hentryMemoryReads : Mem.Reads entry.memory entryImage)
    (hchild : PrimaryChildExecution sevm post) :
    Devm.getStor post upgradeProxy =
        ((((Devm.getStor entry upgradeProxy).set implementationSlotLit
          v2Implementation.toB256).set v2ValueSlot
            (Devm.getStorVal entry upgradeProxy v1ValueSlot)).set
              migrationMarkerSlot migrationMarkerValue) ∧
      storageWord post.state upgradeProxy implementationSlotLit =
        v2Implementation.toB256 ∧
      storageWord post.state upgradeProxy v1ValueSlot =
        storageWord entry.state upgradeProxy v1ValueSlot ∧
      storageWord post.state upgradeProxy v2ValueSlot =
        storageWord entry.state upgradeProxy v1ValueSlot ∧
      storageWord post.state upgradeProxy migrationMarkerSlot =
        migrationMarkerValue ∧
      initializedDomain upgradeProxy post.state ∧
      upgradeRelation upgradeProxy entry.state post.state ∧
      post.logs = entry.logs ++
        [rawUpgradedLog upgradeProxy v2Implementation.toB256] := by
  have proxyRun : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post) := by
    simpa [hproxy] using houter
  have _callerExact : sevm.caller = upgradeAdmin := hcaller
  have _v1Exact := hv1Installed
  have _v2CodeExact := hv2Code
  obtain ⟨checkPre, afterPre, delegatePre, decodedImage,
      entryCheckStor, entryCheckLogs, commitStor, commitLogs, setupState,
      setupLogs, boundary⟩ :=
    primary_outer_boundary_of_program proxyRun hentryStack hvalue hdata
      hauthorized hliveAdmin hrawCommit hentryMemoryWf hentryMemoryReads
  rcases boundary with
    ⟨gasWord, callPre, callPost, callRun, tailRun, stack, memoryWf,
      memoryReads, boundaryState, boundaryLogs⟩
  rcases hchild delegatePre decodedImage gasWord callPre callPost callRun
      tailRun stack memoryWf memoryReads boundaryState boundaryLogs with
    ⟨spawn, child, callRun', tailRun', codeWord, resolved, code, childData,
      settled, childRun⟩
  have _callExact := callRun'
  have _codeWordExact := codeWord
  have _resolvedExact := resolved
  have _codeExact := code
  have childData' : (initSevm spawn.child).data =
      initializeV2Calldata := by
    simpa only [initSevm] using childData
  have childSelector : Sevm.selector (initSevm spawn.child) =
      initializeV2Selector := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
        (selected := initializeV2Selector) (tail := [])
    · rfl
    · simpa [initializeV2Calldata] using childData'
  have childEffect := v2_initializer_run_storage_effect childRun rfl
    childSelector
  have success := upgradeToAndCallDelegateTail_success_state settled tailRun'
  have childInitialState : (initDevm spawn.child).state =
      afterPre.state := by
    calc
      (initDevm spawn.child).state = spawn.parent.state := rfl
      _ = callPre.state :=
        Blanc.ProxyPair.Upgrade.DelegatecallSpawnDescriptor.parent_state_eq_callPre
          spawn
      _ = delegatePre.state := boundaryState.symm
      _ = afterPre.state := setupState.symm
  have entryAfterStor : Devm.getStor afterPre sevm.currentTarget =
      (Devm.getStor entry sevm.currentTarget).set implementationSlotLit
        v2Implementation.toB256 := by
    rw [commitStor, ← congrFun entryCheckStor sevm.currentTarget]
  have childInitialStor : Devm.getStor (initDevm spawn.child)
      sevm.currentTarget =
      (Devm.getStor entry sevm.currentTarget).set implementationSlotLit
        v2Implementation.toB256 := by
    rw [funext (getStor_eq_of_state_eq childInitialState)]
    exact entryAfterStor
  have postChildStor : Devm.getStor post sevm.currentTarget =
      Devm.getStor child sevm.currentTarget :=
    congrFun (funext (getStor_eq_of_state_eq success.2.1))
      sevm.currentTarget
  have childEffect' : Devm.getStor child sevm.currentTarget =
      ((Devm.getStor (initDevm spawn.child) sevm.currentTarget).set
        v2ValueSlot
          (Devm.getStorVal (initDevm spawn.child)
            sevm.currentTarget v1ValueSlot)).set
        migrationMarkerSlot migrationMarkerValue := by
    simpa using childEffect.1
  have initialV1 : Devm.getStorVal (initDevm spawn.child)
      sevm.currentTarget v1ValueSlot =
      Devm.getStorVal entry sevm.currentTarget v1ValueSlot := by
    change (Devm.getStor (initDevm spawn.child) sevm.currentTarget).get
        v1ValueSlot =
      (Devm.getStor entry sevm.currentTarget).get v1ValueSlot
    rw [childInitialStor, Stor.get_set_ne _
      (show implementationSlotLit ≠ v1ValueSlot by decide)]
  have finalStorAtOwner : Devm.getStor post sevm.currentTarget =
      ((((Devm.getStor entry sevm.currentTarget).set
        implementationSlotLit v2Implementation.toB256).set v2ValueSlot
          (Devm.getStorVal entry sevm.currentTarget v1ValueSlot)).set
            migrationMarkerSlot migrationMarkerValue) := by
    rw [postChildStor, childEffect', childInitialStor, initialV1]
  have childLogsEmpty : child.logs = [] := by
    calc
      child.logs = (initDevm spawn.child).logs := childEffect.2
      _ = [] := rfl
  have parentLogs : spawn.parent.logs = afterPre.logs :=
    (Blanc.ProxyPair.Upgrade.DelegatecallSpawnDescriptor.parent_logs_eq_callPre
      spawn).trans (boundaryLogs.symm.trans setupLogs.symm)
  have postLogsAtEntry : post.logs = entry.logs ++
      [rawUpgradedLog sevm.currentTarget v2Implementation.toB256] := by
    rw [success.2.2, childLogsEmpty, List.append_nil, parentLogs,
      commitLogs, ← entryCheckLogs]
  rw [howner] at finalStorAtOwner
  refine ⟨finalStorAtOwner, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get implementationSlotLit = _
    rw [finalStorAtOwner,
      Stor.get_set_ne _
        (show migrationMarkerSlot ≠ implementationSlotLit by decide),
      Stor.get_set_ne _
        (show v2ValueSlot ≠ implementationSlotLit by decide),
      Stor.get_set_self]
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get v1ValueSlot =
      (Devm.getStor entry upgradeProxy).get v1ValueSlot
    rw [finalStorAtOwner,
      Stor.get_set_ne _
        (show migrationMarkerSlot ≠ v1ValueSlot by decide),
      Stor.get_set_ne _ (show v2ValueSlot ≠ v1ValueSlot by decide),
      Stor.get_set_ne _
        (show implementationSlotLit ≠ v1ValueSlot by decide)]
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get v2ValueSlot =
      (Devm.getStor entry upgradeProxy).get v1ValueSlot
    rw [finalStorAtOwner,
      Stor.get_set_ne _
        (show migrationMarkerSlot ≠ v2ValueSlot by decide),
      Stor.get_set_self]
    rfl
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get migrationMarkerSlot = _
    rw [finalStorAtOwner, Stor.get_set_self]
  · unfold initializedDomain storageWord
    change (Devm.getStor post upgradeProxy).get migrationMarkerSlot = _
    rw [finalStorAtOwner, Stor.get_set_self]
  · unfold upgradeRelation storageWord
    change (Devm.getStor entry upgradeProxy).get v1ValueSlot =
      (Devm.getStor post upgradeProxy).get v2ValueSlot
    rw [finalStorAtOwner,
      Stor.get_set_ne _
        (show migrationMarkerSlot ≠ v2ValueSlot by decide),
      Stor.get_set_self]
    rfl
  · simpa [howner] using postLogsAtEntry

/-! ## Identity routes -/

/-- The public `upgradeTo` walk reaches the exact implementation-control body
while retaining the entry storage map.  The existing generic consumer drops
this equality, so the product proof keeps the stronger route field. -/
private theorem upgradeTo_authorized_reaches_code_check_with_storage
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
        ([] : Stack) <<+ checkPre.stack ∧
        Devm.getStor entry = Devm.getStor checkPre := by
  obtain ⟨authPre, route, entryAuthStor⟩ :=
    upgradeTo_activeAdminRoute_of_program hprog hentryStack hvalue hdata
  have adminAtAuth : storedAdminWord entry sevm.currentTarget =
      storedAdminWord authPre sevm.currentTarget :=
    storedAdminWord_eq_of_getStor_eq entryAuthStor
  have authNonzero : storedAdminWord authPre sevm.currentTarget ≠ 0 := by
    intro zero
    exact adminNonzero (adminAtAuth.trans zero)
  have authEqCaller : storedAdminWord authPre sevm.currentTarget =
      sevm.caller.toB256 := adminAtAuth.symm.trans adminEqCaller
  cases route with
  | ossified _ adminZero _ _ _ _ _ =>
      exact (authNonzero adminZero).elim
  | authorized checkPre _ _ checkRun stack storage _ _ =>
      exact ⟨checkPre, checkRun, stack, entryAuthStor.trans storage⟩
  | unauthorized _ _ adminNeCaller _ _ _ _ _ =>
      exact (adminNeCaller authEqCaller).elim

/-- An exact compiled `upgradeTo` execution changes only the ERC-1967
implementation word in the application storage map.  The old implementation,
new code installation, authorization, emitted event, and exact proxy program
are all visible in the statement. -/
theorem upgradeTo_realizes_identity
    (proxyProg : Prog) (hproxy : proxyProg = runtimeBaseline)
    {sevm : Sevm} {entry post : Devm}
    (houter : Prog.RunCompiledTo sevm entry proxyProg (.ok post))
    (howner : sevm.currentTarget = upgradeProxy)
    (hcaller : sevm.caller = upgradeAdmin)
    (hdata : sevm.data = proxyUpgradeToCalldata v2Implementation)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hauthorized : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256)
    (hliveAdmin : storedAdminWord entry sevm.currentTarget ≠ 0)
    (hv1Installed : storedImplementationWord entry sevm.currentTarget =
      v1Implementation.toB256)
    (hv2Code : entry.getCode v2Implementation = v2Code)
    (hrawCommit : addressSlotUpdateRaw entry sevm.currentTarget
      implementationSlotLit v2Implementation.toB256 =
        v2Implementation.toB256) :
    ∃ checkPre,
      Func.RunCompiledTo
          (runtimeBaseline.main :: runtimeBaseline.aux)
          sevm checkPre (upgradeImplementationControl Func.stop) (.ok post) ∧
        Devm.getStor entry = Devm.getStor checkPre ∧
        (checkPre.getCode v2Implementation).size.toB256 ≠ 0 ∧
        post.logs = checkPre.logs ++
          [rawUpgradedLog sevm.currentTarget v2Implementation.toB256] ∧
        Devm.getStor post upgradeProxy =
          (Devm.getStor entry upgradeProxy).set implementationSlotLit
            v2Implementation.toB256 ∧
        storageWord post.state upgradeProxy implementationSlotLit =
          v2Implementation.toB256 ∧
        storageWord post.state upgradeProxy v1ValueSlot =
          storageWord entry.state upgradeProxy v1ValueSlot ∧
        storageWord post.state upgradeProxy v2ValueSlot =
          storageWord entry.state upgradeProxy v2ValueSlot ∧
        storageWord post.state upgradeProxy migrationMarkerSlot =
          storageWord entry.state upgradeProxy migrationMarkerSlot := by
  have proxyRun : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post) := by
    simpa [hproxy] using houter
  have _callerExact : sevm.caller = upgradeAdmin := hcaller
  have _v1Exact := hv1Installed
  have _v2CodeExact := hv2Code
  obtain ⟨checkPre, checkRun, pCheck, entryCheckStor⟩ :=
    upgradeTo_authorized_reaches_code_check_with_storage proxyRun
      hentryStack hvalue hdata hliveAdmin hauthorized
  have effect := upgradeImplementationControl_success
    (fs := runtimeBaseline.main :: runtimeBaseline.aux)
    (by simp [runtimeBaseline, runtimeBaselineAux,
      noCodeImplementationErrorSlot, noCodeImplementationError])
    pCheck checkRun
  have arg0 : Sevm.argWord sevm 0 = v2Implementation.toB256 :=
    proxyUpgradeToCalldata_arg0 hdata
  have checkRawCommit : addressSlotUpdateRaw checkPre sevm.currentTarget
      implementationSlotLit v2Implementation.toB256 =
        v2Implementation.toB256 := by
    have rawWordEq : checkPre.getStorVal sevm.currentTarget
        implementationSlotLit =
        entry.getStorVal sevm.currentTarget implementationSlotLit := by
      change (Devm.getStor checkPre sevm.currentTarget).get
          implementationSlotLit =
        (Devm.getStor entry sevm.currentTarget).get implementationSlotLit
      rw [← congrFun entryCheckStor sevm.currentTarget]
    unfold addressSlotUpdateRaw at hrawCommit ⊢
    rw [rawWordEq]
    exact hrawCommit
  have codePresent :
      (checkPre.getCode v2Implementation).size.toB256 ≠ 0 := by
    simpa only [arg0, toAdr_toB256] using effect.1
  have logs : post.logs = checkPre.logs ++
      [rawUpgradedLog sevm.currentTarget v2Implementation.toB256] := by
    simpa [arg0] using effect.2.2
  have finalStorCurrent : Devm.getStor post sevm.currentTarget =
      (Devm.getStor entry sevm.currentTarget).set implementationSlotLit
        v2Implementation.toB256 := by
    rw [effect.2.1, arg0, checkRawCommit,
      ← congrFun entryCheckStor sevm.currentTarget]
  rw [howner] at finalStorCurrent
  refine ⟨checkPre, checkRun, entryCheckStor, codePresent, logs,
    finalStorCurrent, ?_, ?_, ?_, ?_⟩
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get implementationSlotLit = _
    rw [finalStorCurrent, Stor.get_set_self]
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get v1ValueSlot =
      (Devm.getStor entry upgradeProxy).get v1ValueSlot
    rw [finalStorCurrent, Stor.get_set_ne _
      (show implementationSlotLit ≠ v1ValueSlot by decide)]
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get v2ValueSlot =
      (Devm.getStor entry upgradeProxy).get v2ValueSlot
    rw [finalStorCurrent, Stor.get_set_ne _
      (show implementationSlotLit ≠ v2ValueSlot by decide)]
  · unfold storageWord
    change (Devm.getStor post upgradeProxy).get migrationMarkerSlot =
      (Devm.getStor entry upgradeProxy).get migrationMarkerSlot
    rw [finalStorCurrent, Stor.get_set_ne _
      (show implementationSlotLit ≠ migrationMarkerSlot by decide)]

/-- The decoded empty/false `upgradeToAndCall` branch reaches `STOP` without
spawning a child.  Its application-storage effect is therefore the same
identity specialization as `upgradeTo`: only the implementation word differs
from the entry map. -/
theorem upgradeToAndCall_skipped_empty_realizes_identity
    (proxyProg : Prog) (hproxy : proxyProg = runtimeBaseline)
    {sevm : Sevm} {entry checkPre post : Devm} {decodedImage : Bytes}
    (houter : Prog.RunCompiledTo sevm entry proxyProg (.ok post))
    (howner : sevm.currentTarget = upgradeProxy)
    (hcaller : sevm.caller = upgradeAdmin)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      v2Implementation [] false)
    (hauthorized : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256)
    (hliveAdmin : storedAdminWord entry sevm.currentTarget ≠ 0)
    (hv1Installed : storedImplementationWord entry sevm.currentTarget =
      v1Implementation.toB256)
    (hv2Code : entry.getCode v2Implementation = v2Code)
    (hentryCheck : Devm.getStor entry = Devm.getStor checkPre)
    (hcommitValue : addressSlotUpdateRaw checkPre sevm.currentTarget
      implementationSlotLit (Sevm.argWord sevm 0) =
        v2Implementation.toB256)
    (route : UpgradeToAndCallCommittedRoute
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm checkPre decodedImage [] false (.ok post)) :
    Devm.getStor post upgradeProxy =
        (Devm.getStor entry upgradeProxy).set implementationSlotLit
          v2Implementation.toB256 ∧
      storageWord post.state upgradeProxy v1ValueSlot =
        storageWord entry.state upgradeProxy v1ValueSlot ∧
      storageWord post.state upgradeProxy v2ValueSlot =
        storageWord entry.state upgradeProxy v2ValueSlot ∧
      storageWord post.state upgradeProxy migrationMarkerSlot =
        storageWord entry.state upgradeProxy migrationMarkerSlot := by
  have _proxyRun : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post) := by
    simpa [hproxy] using houter
  have _callerExact : sevm.caller = upgradeAdmin := hcaller
  have _dataExact := hdata
  have _authorizedExact := hauthorized
  have _liveExact := hliveAdmin
  have _v1Exact := hv1Installed
  have _v2CodeExact := hv2Code
  rcases route with
    ⟨afterPre, afterRun, pAfter, committedStor, committedLogs,
      committedMemory, setupRoute⟩
  have _afterExact := afterRun
  have _stackExact := pAfter
  have _logsExact := committedLogs
  have _memoryExact := committedMemory
  cases setupRoute with
  | nonempty setupNonempty _ _ _ _ _ _ =>
      exact (setupNonempty rfl).elim
  | forced _ forceTrue _ _ _ _ _ _ =>
      simp at forceTrue
  | skipped _ _ stopPre stopRun _ _ _ setupState =>
      have postEq : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
      have postAfterState : post.state = afterPre.state := by
        rw [postEq]
        exact setupState.symm
      have postAfterStor : Devm.getStor post = Devm.getStor afterPre :=
        funext (getStor_eq_of_state_eq postAfterState)
      have finalStorCurrent : Devm.getStor post sevm.currentTarget =
          (Devm.getStor entry sevm.currentTarget).set
            implementationSlotLit v2Implementation.toB256 := by
        calc
          Devm.getStor post sevm.currentTarget =
              Devm.getStor afterPre sevm.currentTarget :=
            congrFun postAfterStor sevm.currentTarget
          _ = (Devm.getStor checkPre sevm.currentTarget).set
                implementationSlotLit v2Implementation.toB256 := by
            rw [committedStor, hcommitValue]
          _ = (Devm.getStor entry sevm.currentTarget).set
                implementationSlotLit v2Implementation.toB256 := by
            rw [hentryCheck]
      rw [howner] at finalStorCurrent
      refine ⟨finalStorCurrent, ?_, ?_, ?_⟩
      · unfold storageWord
        change (Devm.getStor post upgradeProxy).get v1ValueSlot =
          (Devm.getStor entry upgradeProxy).get v1ValueSlot
        rw [finalStorCurrent, Stor.get_set_ne _
          (show implementationSlotLit ≠ v1ValueSlot by decide)]
      · unfold storageWord
        change (Devm.getStor post upgradeProxy).get v2ValueSlot =
          (Devm.getStor entry upgradeProxy).get v2ValueSlot
        rw [finalStorCurrent, Stor.get_set_ne _
          (show implementationSlotLit ≠ v2ValueSlot by decide)]
      · unfold storageWord
        change (Devm.getStor post upgradeProxy).get migrationMarkerSlot =
          (Devm.getStor entry upgradeProxy).get migrationMarkerSlot
        rw [finalStorCurrent, Stor.get_set_ne _
          (show implementationSlotLit ≠ migrationMarkerSlot by decide)]

/-- Preserving the three application words is R2-sound precisely when the
unchanged prestate was already admitted by the initialized v2 domain. -/
theorem upgradeTo_identity_sound_of_admissible
    {proxy : Adr} {pre post : State}
    (admissible : identityAdmissible proxy pre)
    (_s1 : storageWord post proxy v1ValueSlot =
      storageWord pre proxy v1ValueSlot)
    (s2 : storageWord post proxy v2ValueSlot =
      storageWord pre proxy v2ValueSlot)
    (marker : storageWord post proxy migrationMarkerSlot =
      storageWord pre proxy migrationMarkerSlot) :
    initializedDomain proxy post ∧ upgradeRelation proxy pre post := by
  constructor
  · unfold initializedDomain
    rw [marker]
    exact admissible.1
  · unfold upgradeRelation
    rw [s2]
    exact admissible.2

end Blanc.ProxyPair.Upgrade
