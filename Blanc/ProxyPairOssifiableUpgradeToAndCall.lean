import Blanc.ProxyPairOssifiableControlEffects
import Blanc.DelegatecallEnvelope

/-!
# OssifiableProxy `upgradeToAndCall` execution and settlement

This module composes the decoded and authorized control route with the exact
implementation commit and the optional setup `DELEGATECALL`.  The lower
control-effects module deliberately stops at raw body boundaries; this module
opens the child frame and records the settlement behavior needed by the public
program theorems.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Blanc.Ninst
open scoped LogOutputHinv

namespace ProxyPair

/-! ## Implementation commit with an arbitrary continuation -/

/-- Exact boundary after the implementation write and `Upgraded` event, just
before an arbitrary continuation begins. -/
inductive UpgradeImplementationCommitBoundary
    (fs : List Func) (sevm : Sevm) (pre : Devm) (continuation : Func)
    (tail : Stack) (out : Execution) : Prop
  | intro (continuationPre : Devm)
      (continuationRun : Func.RunCompiledTo fs sevm continuationPre
        continuation out)
      (stack : tail <<+ continuationPre.stack)
      (storage :
        Devm.getStor continuationPre sevm.currentTarget =
          (Devm.getStor pre sevm.currentTarget).set implementationSlotLit
            (addressSlotUpdateRaw pre sevm.currentTarget
              implementationSlotLit (Sevm.argWord sevm 0)))
      (logs : continuationPre.logs = pre.logs ++
        [rawUpgradedLog sevm.currentTarget (Sevm.argWord sevm 0)])
      (memory : continuationPre.memory = pre.memory)

/-- Open the product-specific implementation commit while retaining its
arbitrary continuation and exact storage/log/memory boundary. -/
theorem upgradeImplementationCommit_boundary
    {fs : List Func} {sevm : Sevm} {pre : Devm} {continuation : Func}
    {tail : Stack} {out : Execution}
    (hp : Sevm.argWord sevm 0 :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeImplementationCommit continuation) out) :
    UpgradeImplementationCommitBoundary fs sevm pre continuation tail out := by
  rcases upgradeImplementationWordCommit_boundary hp run with
    ⟨continuationPre, continuationRun, pContinuation, storage, logs,
      memory⟩
  exact .intro continuationPre continuationRun pContinuation storage logs
    memory

/-- A code-present implementation-control walk necessarily crosses the exact
commit boundary and reaches its arbitrary continuation. -/
theorem upgradeImplementationControl_codePresent_boundary
    {fs : List Func} {sevm : Sevm} {pre : Devm} {continuation : Func}
    {tail : Stack} {out : Execution}
    (hp : tail <<+ pre.stack)
    (codePresent :
      (pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 ≠ 0)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeImplementationControl continuation) out) :
    UpgradeImplementationCommitBoundary fs sevm pre continuation tail out := by
  rcases upgradeImplementationControl_route hp run with
    ⟨codeZero, _, _, _, _, _, _⟩ |
      ⟨_, commitPre, commitRun, pCommit, commitStor, commitLogs,
        commitMemory⟩
  · exact (codePresent codeZero).elim
  · rcases upgradeImplementationCommit_boundary pCommit commitRun with
      ⟨continuationPre, continuationRun, pContinuation, storage, logs,
        memory⟩
    refine .intro continuationPre continuationRun pContinuation ?_ ?_ ?_
    · rw [storage]
      unfold addressSlotUpdateRaw
      rw [← congrFun commitStor sevm.currentTarget]
      have hvalue :
          commitPre.getStorVal sevm.currentTarget implementationSlotLit =
            pre.getStorVal sevm.currentTarget implementationSlotLit := by
        change
          (Devm.getStor commitPre sevm.currentTarget).get
              implementationSlotLit =
            (Devm.getStor pre sevm.currentTarget).get implementationSlotLit
        rw [← congrFun commitStor sevm.currentTarget]
      rw [hvalue]
    · rw [logs, commitLogs]
    · exact memory.trans commitMemory.symm

/-! ## Decoded public route into authorization -/

/-- The canonical decoder boundary followed by the exact active-admin route.
The decoder's written memory image is retained at the authorization entry. -/
inductive UpgradeToAndCallDecodedRoute
    (fs : List Func) (sevm : Sevm) (decodePre : Devm) (image : Bytes)
    (newImplementation : Adr) (setupCalldata : Bytes) (forceCall : Bool)
    (out : Execution) : Prop
  | intro (authPre : Devm)
      (route : ActiveAdminRoute fs sevm authPre
        (upgradeImplementationControl upgradeToAndCallAfter) [] out)
      (memoryWf : Mem.Wf authPre.memory)
      (memoryReads : Mem.Reads authPre.memory
        (upgradeToAndCallDecodedImage image newImplementation setupCalldata
          forceCall))
      (state : decodePre.state = authPre.state)

/-- Open the exact public `upgradeToAndCall` program through ABI decoding and
authorization classification.  Memory-side premises are requested only after
the concrete endpoint entry has been recovered. -/
theorem upgradeToAndCall_decoded_route_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hlength64 : setupCalldata.length < 2 ^ 64)
    (hdataLength : 132 + ceil32 setupCalldata.length < 2 ^ 256) :
    ∃ decodePre,
      Devm.getStor entry = Devm.getStor decodePre ∧
      ∀ image : Bytes, Mem.Wf decodePre.memory →
        Mem.Reads decodePre.memory image →
        UpgradeToAndCallDecodedRoute
          (runtimeBaseline.main :: runtimeBaseline.aux)
          sevm decodePre image newImplementation setupCalldata forceCall
          out := by
  obtain ⟨decodePre, decodeRun, pDecode, decodeStor⟩ :=
    upgradeToAndCall_body_of_program hprog hentryStack hvalue hdata
  rw [upgradeToAndCall_control_shape] at decodeRun
  refine ⟨decodePre, decodeStor, ?_⟩
  intro image hwf hreads
  rcases decodeUpgradeToAndCallControl_boundary pDecode hwf hreads hdata
      hlength64 hdataLength decodeRun with
    ⟨authPre, authRun, pAuth, authWf, authReads, decodeState⟩
  exact .intro authPre (activeAdminControl_route pAuth authRun)
    authWf authReads decodeState

/-- The decoded public route preserves enough memory evidence to classify the
ossified-precedence arm all the way through its exact custom-error payload. -/
theorem UpgradeToAndCallDecodedRoute.ossified_exact
    {sevm : Sevm} {decodePre : Devm} {image : Bytes}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    {out : Execution}
    (route : UpgradeToAndCallDecodedRoute
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm decodePre image newImplementation setupCalldata forceCall out)
    (adminZero : storedAdminWord decodePre sevm.currentTarget = 0) :
    ∃ callPre,
      Func.RunCompiledTo
          (runtimeBaseline.main :: runtimeBaseline.aux)
          sevm callPre (.call proxyIsOssifiedErrorSlot) out ∧
        ControlErrorOutcome callPre proxyIsOssifiedErrorData out := by
  rcases route with
    ⟨authPre, authRoute, authWf, authReads, decodeState⟩
  have decodeAuthStor : Devm.getStor decodePre = Devm.getStor authPre :=
    funext (getStor_eq_of_state_eq decodeState)
  have hadmin := storedAdminWord_eq_of_getStor_eq decodeAuthStor
    (owner := sevm.currentTarget)
  have authZero : storedAdminWord authPre sevm.currentTarget = 0 :=
    hadmin.symm.trans adminZero
  cases authRoute with
  | ossified callPre _ callRun _ _ memory _ =>
      have callWf : Mem.Wf callPre.memory := by
        rw [← memory]
        exact authWf
      have callReads : Mem.Reads callPre.memory
          (upgradeToAndCallDecodedImage image newImplementation setupCalldata
            forceCall) := by
        rw [← memory]
        exact authReads
      exact ⟨callPre, callRun,
        proxyIsOssified_call_exact callWf callReads callRun⟩
  | authorized _ adminNonzero _ _ _ _ _ _ =>
      exact (adminNonzero authZero).elim
  | unauthorized _ adminNonzero _ _ _ _ _ _ =>
      exact (adminNonzero authZero).elim

/-- A live mismatching caller on the decoded public route reaches the exact
`NotAdmin` payload, not merely the named auxiliary call. -/
theorem UpgradeToAndCallDecodedRoute.unauthorized_exact
    {sevm : Sevm} {decodePre : Devm} {image : Bytes}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    {out : Execution}
    (route : UpgradeToAndCallDecodedRoute
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm decodePre image newImplementation setupCalldata forceCall out)
    (adminNonzero : storedAdminWord decodePre sevm.currentTarget ≠ 0)
    (adminNeCaller : storedAdminWord decodePre sevm.currentTarget ≠
      sevm.caller.toB256) :
    ∃ callPre,
      Func.RunCompiledTo
          (runtimeBaseline.main :: runtimeBaseline.aux)
          sevm callPre (.call notAdminErrorSlot) out ∧
        ControlErrorOutcome callPre notAdminErrorData out := by
  rcases route with
    ⟨authPre, authRoute, authWf, authReads, decodeState⟩
  have decodeAuthStor : Devm.getStor decodePre = Devm.getStor authPre :=
    funext (getStor_eq_of_state_eq decodeState)
  have hadmin := storedAdminWord_eq_of_getStor_eq decodeAuthStor
    (owner := sevm.currentTarget)
  have authNonzero : storedAdminWord authPre sevm.currentTarget ≠ 0 := by
    intro hzero
    exact adminNonzero (hadmin.trans hzero)
  have authNeCaller : storedAdminWord authPre sevm.currentTarget ≠
      sevm.caller.toB256 := by
    intro heq
    exact adminNeCaller (hadmin.trans heq)
  cases authRoute with
  | ossified _ authZero _ _ _ _ _ =>
      exact (authNonzero authZero).elim
  | authorized _ _ authEqCaller _ _ _ _ _ =>
      exact (authNeCaller authEqCaller).elim
  | unauthorized callPre _ _ callRun _ _ memory _ =>
      have callWf : Mem.Wf callPre.memory := by
        rw [← memory]
        exact authWf
      have callReads : Mem.Reads callPre.memory
          (upgradeToAndCallDecodedImage image newImplementation setupCalldata
            forceCall) := by
        rw [← memory]
        exact authReads
      exact ⟨callPre, callRun, notAdmin_call_exact callWf callReads callRun⟩

/-- At the compiled public entry, a zero admin selects `ProxyIsOssified`
before caller comparison and fixes its exact custom-error bytes. -/
theorem upgradeToAndCall_ossified_exact_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hlength64 : setupCalldata.length < 2 ^ 64)
    (hdataLength : 132 + ceil32 setupCalldata.length < 2 ^ 256)
    (adminZero : storedAdminWord entry sevm.currentTarget = 0) :
    ∃ decodePre,
      Devm.getStor entry = Devm.getStor decodePre ∧
      ∀ image : Bytes, Mem.Wf decodePre.memory →
        Mem.Reads decodePre.memory image →
        ∃ callPre,
          Func.RunCompiledTo
              (runtimeBaseline.main :: runtimeBaseline.aux)
              sevm callPre (.call proxyIsOssifiedErrorSlot) out ∧
            ControlErrorOutcome callPre proxyIsOssifiedErrorData out := by
  obtain ⟨decodePre, entryDecodeStor, decoded⟩ :=
    upgradeToAndCall_decoded_route_of_program hprog hentryStack hvalue hdata
      hlength64 hdataLength
  refine ⟨decodePre, entryDecodeStor, ?_⟩
  intro image hwf hreads
  have hadmin := storedAdminWord_eq_of_getStor_eq entryDecodeStor
    (owner := sevm.currentTarget)
  exact (decoded image hwf hreads).ossified_exact
    (hadmin.symm.trans adminZero)

/-- At the compiled public entry, a live mismatching caller selects `NotAdmin`
and fixes its exact custom-error bytes. -/
theorem upgradeToAndCall_unauthorized_exact_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hlength64 : setupCalldata.length < 2 ^ 64)
    (hdataLength : 132 + ceil32 setupCalldata.length < 2 ^ 256)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminNeCaller : storedAdminWord entry sevm.currentTarget ≠
      sevm.caller.toB256) :
    ∃ decodePre,
      Devm.getStor entry = Devm.getStor decodePre ∧
      ∀ image : Bytes, Mem.Wf decodePre.memory →
        Mem.Reads decodePre.memory image →
        ∃ callPre,
          Func.RunCompiledTo
              (runtimeBaseline.main :: runtimeBaseline.aux)
              sevm callPre (.call notAdminErrorSlot) out ∧
            ControlErrorOutcome callPre notAdminErrorData out := by
  obtain ⟨decodePre, entryDecodeStor, decoded⟩ :=
    upgradeToAndCall_decoded_route_of_program hprog hentryStack hvalue hdata
      hlength64 hdataLength
  refine ⟨decodePre, entryDecodeStor, ?_⟩
  intro image hwf hreads
  have hadmin := storedAdminWord_eq_of_getStor_eq entryDecodeStor
    (owner := sevm.currentTarget)
  have decodeNonzero : storedAdminWord decodePre sevm.currentTarget ≠ 0 := by
    intro hzero
    exact adminNonzero (hadmin.trans hzero)
  have decodeNeCaller : storedAdminWord decodePre sevm.currentTarget ≠
      sevm.caller.toB256 := by
    intro heq
    exact adminNeCaller (hadmin.trans heq)
  exact (decoded image hwf hreads).unauthorized_exact
    decodeNonzero decodeNeCaller

/-- A live matching admin reaches the implementation code check with the
decoder image, storage relation, and memory invariants still available. -/
theorem upgradeToAndCall_authorized_reaches_code_check
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hlength64 : setupCalldata.length < 2 ^ 64)
    (hdataLength : 132 + ceil32 setupCalldata.length < 2 ^ 256)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ decodePre,
      Devm.getStor entry = Devm.getStor decodePre ∧
      ∀ image : Bytes, Mem.Wf decodePre.memory →
        Mem.Reads decodePre.memory image →
        ∃ checkPre,
          Func.RunCompiledTo
              (runtimeBaseline.main :: runtimeBaseline.aux)
              sevm checkPre
                (upgradeImplementationControl upgradeToAndCallAfter) out ∧
            ([] : Stack) <<+ checkPre.stack ∧
            Mem.Wf checkPre.memory ∧
            Mem.Reads checkPre.memory
              (upgradeToAndCallDecodedImage image newImplementation
                setupCalldata forceCall) ∧
            Devm.getStor entry = Devm.getStor checkPre := by
  obtain ⟨decodePre, entryDecodeStor, decoded⟩ :=
    upgradeToAndCall_decoded_route_of_program hprog hentryStack hvalue hdata
      hlength64 hdataLength
  refine ⟨decodePre, entryDecodeStor, ?_⟩
  intro image hwf hreads
  rcases decoded image hwf hreads with
    ⟨authPre, route, authWf, authReads, decodeState⟩
  have entryAuthStor : Devm.getStor entry = Devm.getStor authPre :=
    entryDecodeStor.trans (funext (getStor_eq_of_state_eq decodeState))
  have hadmin : storedAdminWord entry sevm.currentTarget =
      storedAdminWord authPre sevm.currentTarget :=
    storedAdminWord_eq_of_getStor_eq entryAuthStor
  have authNonzero : storedAdminWord authPre sevm.currentTarget ≠ 0 := by
    intro hzero
    exact adminNonzero (hadmin.trans hzero)
  have authEqCaller : storedAdminWord authPre sevm.currentTarget =
      sevm.caller.toB256 :=
    hadmin.symm.trans adminEqCaller
  cases route with
  | ossified _ authZero _ _ _ _ _ =>
      exact (authNonzero authZero).elim
  | authorized checkPre _ _ checkRun pCheck checkStor checkMemory _ =>
      refine ⟨checkPre, checkRun, pCheck, ?_, ?_,
        entryAuthStor.trans checkStor⟩
      · rw [← checkMemory]
        exact authWf
      · rw [← checkMemory]
        exact authReads
  | unauthorized _ _ authNeCaller _ _ _ _ _ =>
      exact (authNeCaller authEqCaller).elim

/-! ## Committed setup classification -/

/-- Code validation, exact implementation commit, and the exhaustive
skip/nonempty/forced setup classification in one execution-derived boundary. -/
inductive UpgradeToAndCallCommittedRoute
    (fs : List Func) (sevm : Sevm) (checkPre : Devm) (decodedImage : Bytes)
    (setupCalldata : Bytes) (forceCall : Bool) (out : Execution) : Prop
  | intro (afterPre : Devm)
      (afterRun : Func.RunCompiledTo fs sevm afterPre
        upgradeToAndCallAfter out)
      (stack : ([] : Stack) <<+ afterPre.stack)
      (storage :
        Devm.getStor afterPre sevm.currentTarget =
          (Devm.getStor checkPre sevm.currentTarget).set
            implementationSlotLit
            (addressSlotUpdateRaw checkPre sevm.currentTarget
              implementationSlotLit (Sevm.argWord sevm 0)))
      (logs : afterPre.logs = checkPre.logs ++
        [rawUpgradedLog sevm.currentTarget (Sevm.argWord sevm 0)])
      (memory : afterPre.memory = checkPre.memory)
      (setupRoute : UpgradeToAndCallSetupRoute fs sevm afterPre []
        decodedImage setupCalldata forceCall out)

/-- A code-present control walk commits the implementation/event first and
then takes exactly one of the three setup routes. -/
theorem upgradeToAndCall_codePresent_committed_route
    {fs : List Func} {sevm : Sevm} {checkPre : Devm}
    {image : Bytes} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool} {out : Execution}
    (hp : ([] : Stack) <<+ checkPre.stack)
    (hwf : Mem.Wf checkPre.memory)
    (hreads : Mem.Reads checkPre.memory
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall))
    (hlengthBound : setupCalldata.length < 2 ^ 256)
    (codePresent :
      (checkPre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 ≠ 0)
    (run : Func.RunCompiledTo fs sevm checkPre
      (upgradeImplementationControl upgradeToAndCallAfter) out) :
    UpgradeToAndCallCommittedRoute fs sevm checkPre
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall)
      setupCalldata forceCall out := by
  rcases upgradeImplementationControl_codePresent_boundary hp codePresent run
      with
    ⟨afterPre, afterRun, pAfter, storage, logs, memory⟩
  have afterWf : Mem.Wf afterPre.memory := by
    rw [memory]
    exact hwf
  have afterReads : Mem.Reads afterPre.memory
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall) := by
    rw [memory]
    exact hreads
  exact .intro afterPre afterRun pAfter storage logs memory
    (upgradeToAndCallAfter_route pAfter afterWf afterReads hlengthBound
      afterRun)

/-- Exhaustive authorized outcome before setup settlement: absent code reaches
the exact inherited error, while present code commits the implementation/event
and exposes exactly one of the skip, nonempty, or forced-empty setup routes. -/
inductive UpgradeToAndCallAuthorizedOutcome
    (sevm : Sevm) (checkPre : Devm) (decodedImage : Bytes)
    (setupCalldata : Bytes) (forceCall : Bool) (out : Execution) : Prop
  | noCode (callPre : Devm)
      (codeZero :
        (checkPre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 = 0)
      (callRun : Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call noCodeImplementationErrorSlot) out)
      (outcome : ControlErrorOutcome callPre
        noCodeImplementationErrorData out)
  | committed
      (codePresent :
        (checkPre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 ≠ 0)
      (route : UpgradeToAndCallCommittedRoute
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm checkPre decodedImage setupCalldata forceCall out)

/-- Classify the actual authorized implementation check without asking the
consumer to predict whether code is installed. -/
theorem upgradeToAndCall_authorized_outcome
    {sevm : Sevm} {checkPre : Devm} {image : Bytes}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    {out : Execution}
    (hp : ([] : Stack) <<+ checkPre.stack)
    (hwf : Mem.Wf checkPre.memory)
    (hreads : Mem.Reads checkPre.memory
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall))
    (hlengthBound : setupCalldata.length < 2 ^ 256)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm checkPre
        (upgradeImplementationControl upgradeToAndCallAfter) out) :
    UpgradeToAndCallAuthorizedOutcome sevm checkPre
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall)
      setupCalldata forceCall out := by
  rcases upgradeImplementationControl_route hp run with
    ⟨codeZero, callPre, callRun, _, _, _, memory⟩ |
      ⟨codePresent, _, _, _, _, _, _⟩
  · have callWf : Mem.Wf callPre.memory := by
      rw [← memory]
      exact hwf
    have callReads : Mem.Reads callPre.memory
        (upgradeToAndCallDecodedImage image newImplementation setupCalldata
          forceCall) := by
      rw [← memory]
      exact hreads
    exact .noCode callPre codeZero callRun
      (noCodeImplementation_call_exact callWf callReads callRun)
  · exact .committed codePresent
      (upgradeToAndCall_codePresent_committed_route hp hwf hreads
        hlengthBound codePresent run)

/-- Program-level authorized classification through decoding, authorization,
the code check, the exact implementation commit, and all three setup routes. -/
theorem upgradeToAndCall_authorized_outcome_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hlength64 : setupCalldata.length < 2 ^ 64)
    (hdataLength : 132 + ceil32 setupCalldata.length < 2 ^ 256)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ decodePre,
      Devm.getStor entry = Devm.getStor decodePre ∧
      ∀ image : Bytes, Mem.Wf decodePre.memory →
        Mem.Reads decodePre.memory image →
        ∃ checkPre,
          Devm.getStor entry = Devm.getStor checkPre ∧
          UpgradeToAndCallAuthorizedOutcome sevm checkPre
            (upgradeToAndCallDecodedImage image newImplementation
              setupCalldata forceCall)
            setupCalldata forceCall out := by
  obtain ⟨decodePre, entryDecodeStor, reached⟩ :=
    upgradeToAndCall_authorized_reaches_code_check hprog hentryStack hvalue
      hdata hlength64 hdataLength adminNonzero adminEqCaller
  refine ⟨decodePre, entryDecodeStor, ?_⟩
  intro image hwf hreads
  rcases reached image hwf hreads with
    ⟨checkPre, checkRun, pCheck, checkWf, checkReads, entryCheckStor⟩
  exact ⟨checkPre, entryCheckStor,
    upgradeToAndCall_authorized_outcome pCheck checkWf checkReads
      (by omega) checkRun⟩

/-- Same-value implementation upgrades traverse the same exact authorized
classification; there is no equality guard before the code check or commit. -/
theorem upgradeToAndCall_same_value_outcome_of_program
    {sevm : Sevm} {entry : Devm} {out : Execution}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hlength64 : setupCalldata.length < 2 ^ 64)
    (hdataLength : 132 + ceil32 setupCalldata.length < 2 ^ 256)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256)
    (sameValue : newImplementation.toB256 =
      storedImplementationWord entry sevm.currentTarget) :
    ∃ decodePre,
      Devm.getStor entry = Devm.getStor decodePre ∧
      ∀ image : Bytes, Mem.Wf decodePre.memory →
        Mem.Reads decodePre.memory image →
        ∃ checkPre,
          Sevm.argWord sevm 0 =
              storedImplementationWord checkPre sevm.currentTarget ∧
            UpgradeToAndCallAuthorizedOutcome sevm checkPre
              (upgradeToAndCallDecodedImage image newImplementation
                setupCalldata forceCall)
              setupCalldata forceCall out := by
  obtain ⟨decodePre, entryDecodeStor, classified⟩ :=
    upgradeToAndCall_authorized_outcome_of_program hprog hentryStack hvalue
      hdata hlength64 hdataLength adminNonzero adminEqCaller
  refine ⟨decodePre, entryDecodeStor, ?_⟩
  intro image hwf hreads
  rcases classified image hwf hreads with
    ⟨checkPre, entryCheckStor, outcome⟩
  have hstored := storedImplementationWord_eq_of_getStor_eq entryCheckStor
    (owner := sevm.currentTarget)
  exact ⟨checkPre,
    (proxyUpgradeToAndCallCalldata_arg0 hdata).trans
      (sameValue.trans hstored), outcome⟩

/-! ## Exact setup `DELEGATECALL` boundary -/

/-- The post-call branch shared by the nonempty and forced-empty setup arms.
A clean child stops; a failed child first tests the complete returned length,
then bubbles nonempty bytes or calls the inherited empty-error body. -/
def upgradeToAndCallDelegateTail : Func :=
  Func.stop <?>
    (retdatasize :::
      (Func.revReturnData <?> (.call emptyDelegatecallErrorSlot)))

theorem upgradeToAndCallDelegateSetup_split_shape :
    upgradeToAndCallDelegateSetup =
      pushB256 0 :::
      pushB256 0 :::
      loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++
      pushB256 upgradeToAndCallSetupMemoryBase :::
      loadUpgradeToAndCallWord upgradeToAndCallImplementationWord +++
      gas ::: delcall ::: upgradeToAndCallDelegateTail := by
  rfl

/-- Execution-derived setup-call cut.  The boundary retains the exact six
`DELEGATECALL` operands, the actual compiled child step, and the complete
post-call tail.  It deliberately does not assume whether the arbitrary child
succeeds or fails. -/
inductive UpgradeToAndCallDelegateBoundary
    (fs : List Func) (sevm : Sevm) (pre : Devm) (tail : Stack)
    (decodedImage : Bytes) (newImplementation : Adr)
    (setupCalldata : Bytes) (forceCall : Bool) (out : Execution) : Prop
  | intro (gasWord : B256) (callPre callPost : Devm)
      (callRun : Ninst.RunCompiled sevm callPre (.exec .delcall) callPost)
      (tailRun : Func.RunCompiledTo fs sevm callPost
        upgradeToAndCallDelegateTail out)
      (stack :
        gasWord :: newImplementation.toB256 ::
          upgradeToAndCallSetupMemoryBase ::
          Nat.toB256 setupCalldata.length :: 0 :: 0 :: tail <<+
            callPre.stack)
      (memoryWf : Mem.Wf callPre.memory)
      (memoryReads : Mem.Reads callPre.memory decodedImage)
      (state : pre.state = callPre.state)

/-- Once a proof-carrying spawn descriptor is supplied for the exact call
state, the shared inversion theorem retains the arbitrary child execution and
the exact resume equation that produced this boundary's post-call state. -/
theorem UpgradeToAndCallDelegateBoundary.child_certificate
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {decodedImage : Bytes} {newImplementation : Adr}
    {setupCalldata : Bytes} {forceCall : Bool} {out : Execution}
    (boundary : UpgradeToAndCallDelegateBoundary fs sevm pre tail
      decodedImage newImplementation setupCalldata forceCall out) :
    ∃ callPre callPost,
      ∀ spawn : DelegatecallSpawnDescriptor sevm callPre,
        ∃ childOut : MessageResult,
          Nonempty (DelegatedChildCertificate spawn.child childOut) ∧
            spawn.resume.run childOut = .ok callPost := by
  rcases boundary with
    ⟨_, callPre, callPost, callRun, _, _, _, _, _⟩
  exact ⟨callPre, callPost, fun spawn =>
    spawn.certificate_of_runCompiled callRun⟩

/-- Open the runtime setup fragment through the exact compiled
`DELEGATECALL`.  Both scratch-word loads are justified from the canonical
decoder image, so the operand words are derived rather than accepted as
premises. -/
theorem upgradeToAndCallDelegateSetup_boundary
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {image : Bytes} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool} {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall))
    (run : Func.RunCompiledTo fs sevm pre
      upgradeToAndCallDelegateSetup out) :
    UpgradeToAndCallDelegateBoundary fs sevm pre tail
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall)
      newImplementation setupCalldata forceCall out := by
  have himplementationImage : Bytes.toB256
      ((upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall).sliceD 0 32 0) = newImplementation.toB256 := by
    unfold upgradeToAndCallDecodedImage
    rw [Bytes.sliceD_writeAt_before _ _ 0 32 64 (by omega),
      Bytes.sliceD_writeAt_before _ _ 0 32 128 (by omega),
      Bytes.sliceD_writeAt_before _ _ 0 32 32 (by omega),
      Bytes.sliceD_writeAt_before _ _ 0 32 96 (by omega)]
    exact Bytes.readWord_writeAt_self _ 0 newImplementation.toB256
  have hlengthImage : Bytes.toB256
      ((upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall).sliceD 32 32 0) =
      Nat.toB256 setupCalldata.length := by
    unfold upgradeToAndCallDecodedImage
    rw [Bytes.sliceD_writeAt_before _ _ 32 32 64 (by omega),
      Bytes.sliceD_writeAt_before _ _ 32 32 128 (by omega)]
    exact Bytes.readWord_writeAt_self _ 32
      (Nat.toB256 setupCalldata.length)
  rw [upgradeToAndCallDelegateSetup_split_shape] at run
  obtain ⟨zeroOutputOffsetPost, qOutputOffset, run⟩ :=
    runCompiledTo_next_inv run
  obtain ⟨zeroOutputSizePost, qOutputSize, run⟩ :=
    runCompiledTo_next_inv run
  have rOutputOffset := Ninst.Run.of_runCompiled qOutputOffset
  have rOutputSize := Ninst.Run.of_runCompiled qOutputSize
  have pOutputOffset : (0 : B256) :: tail <<+
      zeroOutputOffsetPost.stack :=
    prefix_of_push (of_run_pushB256 rOutputOffset) hp
  have pOutputSize : (0 : B256) :: 0 :: tail <<+
      zeroOutputSizePost.stack :=
    prefix_of_push (of_run_pushB256 rOutputSize) pOutputOffset
  obtain ⟨lengthPost, loadLengthRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pLength, wfLength, readsLength, stateLength⟩ :=
    of_run_loadWordAt_image
      (value := Nat.toB256 setupCalldata.length) pOutputSize
      (by
        rw [← Ninst.Hinv.inv (f := Devm.memory) rOutputSize,
          ← Ninst.Hinv.inv (f := Devm.memory) rOutputOffset]
        exact hwf)
      (by
        rw [← Ninst.Hinv.inv (f := Devm.memory) rOutputSize,
          ← Ninst.Hinv.inv (f := Devm.memory) rOutputOffset]
        exact hreads)
      (by
        rw [show ((upgradeToAndCallSetupLengthWord * 32 : B256)).toNat = 32
          from by decide]
        exact hlengthImage)
      loadLengthRun
  obtain ⟨inputOffsetPost, qInputOffset, run⟩ :=
    runCompiledTo_next_inv run
  have rInputOffset := Ninst.Run.of_runCompiled qInputOffset
  have pInputOffset :
      upgradeToAndCallSetupMemoryBase ::
        Nat.toB256 setupCalldata.length :: 0 :: 0 :: tail <<+
          inputOffsetPost.stack :=
    prefix_of_push (of_run_pushB256 rInputOffset) pLength
  obtain ⟨implementationPost, loadImplementationRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pImplementation, wfImplementation, readsImplementation,
      stateImplementation⟩ :=
    of_run_loadWordAt_image
      (value := newImplementation.toB256) pInputOffset
      (by
        rw [← Ninst.Hinv.inv (f := Devm.memory) rInputOffset]
        exact wfLength)
      (by
        rw [← Ninst.Hinv.inv (f := Devm.memory) rInputOffset]
        exact readsLength)
      (by
        rw [show
          ((upgradeToAndCallImplementationWord * 32 : B256)).toNat = 0
          from by decide]
        exact himplementationImage)
      loadImplementationRun
  obtain ⟨callPre, qGas, run⟩ := runCompiledTo_next_inv run
  have rGas := Ninst.Run.of_runCompiled qGas
  obtain ⟨gasWord, gasPush⟩ := of_run_gas rGas
  have pGas :
      gasWord :: newImplementation.toB256 ::
        upgradeToAndCallSetupMemoryBase ::
        Nat.toB256 setupCalldata.length :: 0 :: 0 :: tail <<+
          callPre.stack :=
    prefix_of_push gasPush pImplementation
  obtain ⟨callPost, callRun, tailRun⟩ := runCompiledTo_next_inv run
  refine .intro gasWord callPre callPost callRun tailRun pGas ?_ ?_ ?_
  · rw [← Ninst.Hinv.inv (f := Devm.memory) rGas]
    exact wfImplementation
  · rw [← Ninst.Hinv.inv (f := Devm.memory) rGas]
    exact readsImplementation
  · exact (Ninst.Hinv.inv (f := Devm.state) rOutputOffset).trans
      ((Ninst.Hinv.inv (f := Devm.state) rOutputSize).trans
        (stateLength.trans
          ((Ninst.Hinv.inv (f := Devm.state) rInputOffset).trans
            (stateImplementation.trans
              gasPush.state))))

/-! ## Setup child settlement -/

/-- The three exact post-setup outcomes.  A clean child reaches `STOP` with
its committed world and logs.  A failed child is already rolled back to the
suspended parent before the runtime distinguishes an empty payload from a
nonempty byte-for-byte bubble. -/
inductive UpgradeToAndCallDelegateOutcome
    {sevm : Sevm} {callPre callPost : Devm}
    (spawn : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (out : Execution) : Prop
  | success (post : Devm)
      (certificate : Nonempty
        (DelegatedChildCertificate spawn.child (.ok child)))
      (childClean : child.error.isSome = false)
      (returnData : callPost.returnData = child.output)
      (outcome : out = .ok post)
      (state : post.state = child.state)
      (transientStorage :
        post.transientStorage = child.transientStorage)
      (logs : post.logs = spawn.parent.logs ++ child.logs)
  | emptyFailure (errorPre : Devm)
      (certificate : Nonempty
        (DelegatedChildCertificate spawn.child (.ok child)))
      (childFailed : child.error.isSome = true)
      (outputEmpty : child.output = [])
      (returnData : callPost.returnData = child.output)
      (callState : callPost.state = spawn.parent.state)
      (callTransientStorage :
        callPost.transientStorage = spawn.parent.transientStorage)
      (callLogs : callPost.logs = spawn.parent.logs)
      (errorEntryState : errorPre.state = callPost.state)
      (outcome : ControlErrorOutcome errorPre
        emptyDelegatecallErrorData out)
  | bubbledFailure (bubblePre : Devm)
      (certificate : Nonempty
        (DelegatedChildCertificate spawn.child (.ok child)))
      (childFailed : child.error.isSome = true)
      (outputNonempty : child.output ≠ [])
      (returnData : callPost.returnData = child.output)
      (callState : callPost.state = spawn.parent.state)
      (callTransientStorage :
        callPost.transientStorage = spawn.parent.transientStorage)
      (callLogs : callPost.logs = spawn.parent.logs)
      (bubbleEntryState : bubblePre.state = callPost.state)
      (outcome :
        (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
          (∃ post, out = .error (.revert, post) ∧
            post.output = child.output))

/-- Expose the exact call states hidden inside the execution-derived setup
cut, then apply the shared retained-child settlement inversion. -/
theorem UpgradeToAndCallDelegateBoundary.settled_child
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {decodedImage : Bytes} {newImplementation : Adr}
    {setupCalldata : Bytes} {forceCall : Bool} {out : Execution}
    (boundary : UpgradeToAndCallDelegateBoundary fs sevm pre tail
      decodedImage newImplementation setupCalldata forceCall out) :
    ∃ callPre callPost,
      Ninst.RunCompiled sevm callPre (.exec .delcall) callPost ∧
      Func.RunCompiledTo fs sevm callPost
        upgradeToAndCallDelegateTail out ∧
      ∀ spawn : DelegatecallSpawnDescriptor sevm callPre,
        spawn.parent.stack.length < 1024 →
          ∃ child, DelegatecallSettledBoundary spawn child callPost := by
  rcases boundary with
    ⟨_, callPre, callPost, callRun, tailRun, _, _, _, _⟩
  exact ⟨callPre, callPost, callRun, tailRun,
    fun spawn room => spawn.settled_of_runCompiled callRun room⟩

/-- Classify the actual OssifiableProxy setup tail from a retained settled
child.  The output-length bound is the honest `B256` round-trip obligation
needed to read nonempty returndata as the same complete byte string. -/
theorem upgradeToAndCallDelegateTail_outcome
    {sevm : Sevm} {callPre callPost : Devm} {child : Devm}
    {image : Bytes} {out : Execution}
    (spawn : DelegatecallSpawnDescriptor sevm callPre)
    (settled : DelegatecallSettledBoundary spawn child callPost)
    (outputLength : child.output.length < 2 ^ 256)
    (memoryWf : Mem.Wf callPost.memory)
    (memoryReads : Mem.Reads callPost.memory image)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm callPost upgradeToAndCallDelegateTail out) :
    UpgradeToAndCallDelegateOutcome (callPost := callPost) spawn child out := by
  rcases settled with
    ⟨certificate, resume, returnData, stack, callState, callTransient,
      callLogs⟩
  obtain ⟨childCertificate⟩ := certificate
  unfold upgradeToAndCallDelegateTail at run
  cases status : child.error.isSome with
  | false =>
      have pOne : (1 : B256) :: spawn.parent.stack <<+ callPost.stack :=
        ⟨[], by simpa [Split, status] using stack⟩
      obtain ⟨stopPre, _, _, branchPop, stopRun, _⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pOne run
      cases out with
      | error error =>
          have terminal := runCompiledTo_last_inv stopRun
          simp [Linst.Run, Linst.run] at terminal
      | ok post =>
          have postEq : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
          refine .success post ⟨childCertificate⟩ status returnData rfl ?_ ?_ ?_
          · rw [postEq]
            exact branchPop.state.symm.trans callState
          · rw [postEq]
            exact branchPop.transientStorage.symm.trans callTransient
          · rw [postEq]
            exact branchPop.logs.symm.trans (by simpa [status] using callLogs)
  | true =>
      have pZero : (0 : B256) :: spawn.parent.stack <<+ callPost.stack :=
        ⟨[], by simpa [Split, status] using stack⟩
      obtain ⟨failedPre, failedPop, failedRun, _⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pZero run
      obtain ⟨sizePost, sizeRun, payloadBranch⟩ :=
        runCompiledTo_next_inv failedRun
      have sizePush := of_run_retdatasize_val
        (Ninst.Run.of_runCompiled sizeRun)
      have failedReturnData : failedPre.returnData = child.output :=
        failedPop.returnData.symm.trans returnData
      have childRollback := childCertificate.rollback_of_error status
      have rolledState : callPost.state = spawn.parent.state :=
        callState.trans (childRollback.1.trans rfl)
      have rolledTransient :
          callPost.transientStorage = spawn.parent.transientStorage :=
        callTransient.trans (childRollback.2.trans rfl)
      have rolledLogs : callPost.logs = spawn.parent.logs := by
        simpa [status] using callLogs
      by_cases outputEmpty : child.output = []
      · have pLengthZero : (0 : B256) :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData, outputEmpty,
              show Nat.toB256 0 = (0 : B256) by decide]
              using sizePush.stack⟩
        obtain ⟨errorPre, errorPop, errorRun, _⟩ :=
          Func.RunCompiledTo.zero_branch_of_prefix pLengthZero payloadBranch
        have errorMemory : errorPre.memory = callPost.memory :=
          errorPop.memory.symm.trans
            (sizePush.memory.symm.trans failedPop.memory.symm)
        have errorState : errorPre.state = callPost.state :=
          errorPop.state.symm.trans
            (sizePush.state.symm.trans failedPop.state.symm)
        have errorWf : Mem.Wf errorPre.memory := by
          rw [errorMemory]
          exact memoryWf
        have errorReads : Mem.Reads errorPre.memory image := by
          rw [errorMemory]
          exact memoryReads
        exact .emptyFailure errorPre ⟨childCertificate⟩ status outputEmpty
          returnData rolledState rolledTransient rolledLogs errorState
          (emptyDelegatecallError_call_exact errorWf errorReads errorRun)
      · have lengthWordNonzero :
            Nat.toB256 child.output.length ≠ 0 := by
          intro hzero
          have hnat := congrArg B256.toNat hzero
          rw [B256.toNat_toB256_of_lt outputLength,
            B256.toNat_zero] at hnat
          exact outputEmpty (List.length_eq_zero_iff.mp hnat)
        have pLength : Nat.toB256 child.output.length :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData] using sizePush.stack⟩
        obtain ⟨bubblePre, _, _, bubblePop, bubbleRun, _⟩ :=
          Func.RunCompiledTo.succ_branch_of_prefix
            lengthWordNonzero pLength payloadBranch
        have bubbleReturnData : bubblePre.returnData = child.output :=
          bubblePop.returnData.symm.trans
            (sizePush.returnData.symm.trans failedReturnData)
        have bubbleState : bubblePre.state = callPost.state :=
          bubblePop.state.symm.trans
            (sizePush.state.symm.trans failedPop.state.symm)
        rcases Func.runCompiledTo_revReturnData_inv bubbleRun with
          outOfGas | ⟨post, postOutcome, postOutput⟩
        · exact .bubbledFailure bubblePre ⟨childCertificate⟩ status
            outputEmpty returnData rolledState rolledTransient rolledLogs
            bubbleState (Or.inl outOfGas)
        · have exactOutput : post.output = child.output := by
            rw [postOutput, bubbleReturnData,
              B256.toNat_toB256_of_lt outputLength, List.take_length]
          exact .bubbledFailure bubblePre ⟨childCertificate⟩ status
            outputEmpty returnData rolledState rolledTransient rolledLogs
            bubbleState (Or.inr ⟨post, postOutcome, exactOutput⟩)

/-- Message settlement restores the complete entry world for any settled
`upgradeToAndCall` failure.  The raw child/tail theorem above identifies why
the frame failed; this theorem supplies the outer-frame atomic rollback. -/
theorem upgradeToAndCall_message_atomicRollback
    {msg : Msg} {xl : Xlot} {out : Devm}
    {newImplementation : Adr} {setupCalldata : Bytes} {forceCall : Bool}
    (data : msg.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (process : ProcessMessage msg xl (.ok out))
    (failed : out.error.isSome) :
    out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage ∧
      msg.data = proxyUpgradeToAndCallCalldata
        newImplementation setupCalldata forceCall := by
  rcases ProcessMessage.rollback_of_error process failed with
    ⟨state, transientStorage⟩
  exact ⟨state, transientStorage, data⟩

end ProxyPair
end Blanc
