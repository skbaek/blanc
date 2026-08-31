import Blanc.ProxyPairUpgradeExecution

/-!
# Compiled through-proxy R2 refinement

The logical R2 theorem is connected here to two actual child executions and
to the exact compiled OssifiableProxy forwarding envelope.  The route records
the EIP-150 gas split, G-5 child budget, depth, warm sets, transfer flag, code
address, target, and proxy storage owner.  `DirectTargetTransport` is
discharged for the scalar input word; no GAS-sensitive implementation claim is
made.
-/

namespace Blanc.ProxyPair.Upgrade

open Jaune

/-- The complete direct/delegated context delta exposed by an exact
OssifiableProxy fallback route. -/
def ExactForwardingContext
    (outer : Msg) {afterTransfer : Benv} {callPre : Devm}
    (spawn : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre) : Prop :=
  spawn.child.currentTarget = outer.currentTarget ∧
    spawn.child.codeAddress = some spawn.resolvedCodeAddress ∧
    spawn.child.gas = spawn.childGas ∧
    spawn.child.depth = outer.depth - 1 ∧
    spawn.child.accessedAddresses = spawn.parent.accessedAddresses ∧
    spawn.child.accessedStorageKeys = spawn.parent.accessedStorageKeys ∧
    spawn.child.accessedAddresses = spawn.afterAccess.accessedAddresses ∧
    spawn.child.accessedStorageKeys =
      spawn.afterAccess.accessedStorageKeys ∧
    spawn.parent.gasLeft = spawn.afterAccess.gasLeft -
      (spawn.callCost + spawn.extensionCost) ∧
    calculateMsgCallGas 0 spawn.gasWord.toNat spawn.afterAccess.gasLeft
      spawn.extensionCost spawn.accessCharge =
        ⟨spawn.callCost, spawn.childGas⟩ ∧
    spawn.child.shouldTransferValue = false ∧
    spawn.child.code = spawn.code

/-- Exact v1 implementation evidence for one shared call.  The compiled walk
and the settled child certificate are both retained.  Output and proxy-owned
storage are derived below from the compiled walk; they are not certificate
fields. -/
structure V1SharedChildExecution
    (msg : Msg) (pre : State) (call : SharedCall) (child : Devm) where
  code : msg.code = v1Code
  data : msg.data = sharedCalldata call
  owner : msg.currentTarget = upgradeProxy
  initialStorage : MessageStorageEqualAt upgradeProxy msg.benv.state pre
  run : Prog.RunCompiledTo (initSevm msg) (initDevm msg) v1Prog (.ok child)
  certificate : DelegatedChildCertificate msg (.ok child)
  clean : child.error.isSome = false

/-- Exact initialized-v2 implementation evidence for one shared call. -/
structure V2SharedChildExecution
    (msg : Msg) (post : State) (call : SharedCall) (child : Devm) where
  code : msg.code = v2Code
  data : msg.data = sharedCalldata call
  owner : msg.currentTarget = upgradeProxy
  initialStorage : MessageStorageEqualAt upgradeProxy msg.benv.state post
  run : Prog.RunCompiledTo (initSevm msg) (initDevm msg) v2Prog (.ok child)
  certificate : DelegatedChildCertificate msg (.ok child)
  clean : child.error.isSome = false

theorem V1SharedChildExecution.compiled_bytes
    {msg : Msg} {pre : State} {call : SharedCall} {child : Devm}
    (execution : V1SharedChildExecution msg pre call child) :
    some msg.code.toList = Prog.compile v1Prog := by
  rw [execution.code, v1Code_toList, v1Prog_compile]

theorem V2SharedChildExecution.compiled_bytes
    {msg : Msg} {post : State} {call : SharedCall} {child : Devm}
    (execution : V2SharedChildExecution msg post call child) :
    some msg.code.toList = Prog.compile v2Prog := by
  rw [execution.code, v2Code_toList, v2Prog_compile]

/-- The v1 child's complete logical effect follows from its exact compiled
walk.  In particular, no caller supplies an output or storage postcondition. -/
theorem V1SharedChildExecution.logical_effect
    {msg : Msg} {pre : State} {call : SharedCall} {child : Devm}
    (execution : V1SharedChildExecution msg pre call child) :
    child.output = (v1Step call pre).2 ∧
      MessageStorageEqualAt upgradeProxy child.state
        (v1Step call pre).1 := by
  cases call with
  | value =>
      have data : (initSevm msg).data = valueCalldata := by
        simpa [initSevm, sharedCalldata] using execution.data
      have effect := v1_value_run_effect execution.run rfl data
      have initialWord :
          (initDevm msg).getStorVal upgradeProxy v1ValueSlot =
            storageWord pre upgradeProxy v1ValueSlot := by
        change (msg.benv.state.get upgradeProxy).stor.get v1ValueSlot =
          (pre.get upgradeProxy).stor.get v1ValueSlot
        exact execution.initialStorage v1ValueSlot
      constructor
      · change child.output =
          (storageWord pre upgradeProxy v1ValueSlot).toBytes
        have outputEffect : child.output =
            ((initDevm msg).getStorVal upgradeProxy v1ValueSlot).toBytes := by
          simpa [ReturnsWord, initSevm, execution.owner] using effect.1
        exact outputEffect.trans (congrArg B256.toBytes initialWord)
      · intro key
        change (Devm.getStor child upgradeProxy).get key =
          (pre.get upgradeProxy).stor.get key
        rw [← congrFun effect.2 upgradeProxy]
        change (msg.benv.state.get upgradeProxy).stor.get key =
          (pre.get upgradeProxy).stor.get key
        exact execution.initialStorage key
  | setValue word =>
      have data : (initSevm msg).data = setValueCalldata word := by
        simpa [initSevm, sharedCalldata] using execution.data
      have effect := v1_setValue_run_effect execution.run rfl data
      have arg : Sevm.argWord (initSevm msg) 0 = word :=
        setValueCalldata_arg0 data
      constructor
      · simpa [v1Step, initDevm, Devm.output] using effect.2
      · intro key
        change (Devm.getStor child upgradeProxy).get key =
          ((pre.setStorVal upgradeProxy v1ValueSlot word).get
            upgradeProxy).stor.get key
        have ownerStorage : Devm.getStor child upgradeProxy =
            (Devm.getStor (initDevm msg) upgradeProxy).set
              v1ValueSlot word := by
          simpa [initSevm, execution.owner, arg] using effect.1
        rw [ownerStorage]
        simp only [State.setStorVal, State.get_set_self]
        by_cases same : key = v1ValueSlot
        · subst key
          rw [Stor.get_set_self, Stor.get_set_self]
        · have different : v1ValueSlot ≠ key := fun equal => same equal.symm
          rw [Stor.get_set_ne _ different, Stor.get_set_ne _ different]
          exact execution.initialStorage key

/-- The initialized-v2 child's complete logical effect is likewise derived
from its exact compiled walk. -/
theorem V2SharedChildExecution.logical_effect
    {msg : Msg} {post : State} {call : SharedCall} {child : Devm}
    (execution : V2SharedChildExecution msg post call child) :
    child.output = (v2Step call post).2 ∧
      MessageStorageEqualAt upgradeProxy child.state
        (v2Step call post).1 := by
  cases call with
  | value =>
      have data : (initSevm msg).data = valueCalldata := by
        simpa [initSevm, sharedCalldata] using execution.data
      have effect := v2_value_run_effect execution.run rfl data
      have initialWord :
          (initDevm msg).getStorVal upgradeProxy v2ValueSlot =
            storageWord post upgradeProxy v2ValueSlot := by
        change (msg.benv.state.get upgradeProxy).stor.get v2ValueSlot =
          (post.get upgradeProxy).stor.get v2ValueSlot
        exact execution.initialStorage v2ValueSlot
      constructor
      · change child.output =
          (storageWord post upgradeProxy v2ValueSlot).toBytes
        have outputEffect : child.output =
            ((initDevm msg).getStorVal upgradeProxy v2ValueSlot).toBytes := by
          simpa [ReturnsWord, initSevm, execution.owner] using effect.1
        exact outputEffect.trans (congrArg B256.toBytes initialWord)
      · intro key
        change (Devm.getStor child upgradeProxy).get key =
          (post.get upgradeProxy).stor.get key
        rw [← congrFun effect.2 upgradeProxy]
        change (msg.benv.state.get upgradeProxy).stor.get key =
          (post.get upgradeProxy).stor.get key
        exact execution.initialStorage key
  | setValue word =>
      have data : (initSevm msg).data = setValueCalldata word := by
        simpa [initSevm, sharedCalldata] using execution.data
      have effect := v2_setValue_run_effect execution.run rfl data
      have arg : Sevm.argWord (initSevm msg) 0 = word :=
        setValueCalldata_arg0 data
      constructor
      · simpa [v2Step, initDevm, Devm.output] using effect.2
      · intro key
        change (Devm.getStor child upgradeProxy).get key =
          ((post.setStorVal upgradeProxy v2ValueSlot word).get
            upgradeProxy).stor.get key
        have ownerStorage : Devm.getStor child upgradeProxy =
            (Devm.getStor (initDevm msg) upgradeProxy).set
              v2ValueSlot word := by
          simpa [initSevm, execution.owner, arg] using effect.1
        rw [ownerStorage]
        simp only [State.setStorVal, State.get_set_self]
        by_cases same : key = v2ValueSlot
        · subst key
          rw [Stor.get_set_self, Stor.get_set_self]
        · have different : v2ValueSlot ≠ key := fun equal => same equal.symm
          rw [Stor.get_set_ne _ different, Stor.get_set_ne _ different]
          exact execution.initialStorage key

/-- All execution-side premises for comparing one v1 and one initialized-v2
call through the same exact proxy program.  Existentials are used instead of
a single deeply dependent record so the public interface remains below the
repository heartbeat ceiling. -/
def ExactProxyPairSharedExecution
    (proxyProg : Prog) (pre post : State) (call : SharedCall) : Prop :=
  proxyProg = runtimeBaseline ∧
    ∃ (outerV1 : Msg) (afterTransferV1 : Benv) (callPreV1 : Devm)
      (spawnV1 : DelegatecallSpawnDescriptor
        (initSevm (outerV1.withBenv afterTransferV1)) callPreV1)
      (routeV1 : OssifiableForwardingRoute outerV1 afterTransferV1
        callPreV1 spawnV1)
      (childV1 : Devm)
      (_implementationV1 : V1SharedChildExecution
        spawnV1.child pre call childV1)
      (_tailV1 : ForwardingTailBudget spawnV1 childV1),
      routeV1.ValidInstallation ∧
        outerV1.currentTarget = upgradeProxy ∧
        spawnV1.resolvedCodeAddress = v1Implementation ∧
        spawnV1.code = v1Code ∧
        ∃ (outerV2 : Msg) (afterTransferV2 : Benv) (callPreV2 : Devm)
          (spawnV2 : DelegatecallSpawnDescriptor
            (initSevm (outerV2.withBenv afterTransferV2)) callPreV2)
          (routeV2 : OssifiableForwardingRoute outerV2 afterTransferV2
            callPreV2 spawnV2)
          (childV2 : Devm)
          (_implementationV2 : V2SharedChildExecution
            spawnV2.child post call childV2)
          (_tailV2 : ForwardingTailBudget spawnV2 childV2),
          routeV2.ValidInstallation ∧
            outerV2.currentTarget = upgradeProxy ∧
            spawnV2.resolvedCodeAddress = v2Implementation ∧
            spawnV2.code = v2Code

/-- Settled wrapper-level result of an exact pair of implementation calls.
The output and R2 relation are stated on the wrappers, not merely their direct
children.  Both direct/delegated scalar-input transports and both complete
context deltas remain inspectable conclusions. -/
def ThroughProxyRefinementResult : Prop :=
  ∃ (outerV1 outerV2 : Msg) (wrapperV1 wrapperV2 : Devm),
    processMessage outerV1 = .ok wrapperV1 ∧
      processMessage outerV2 = .ok wrapperV2 ∧
      wrapperV1.output = wrapperV2.output ∧
      initializedDomain upgradeProxy wrapperV2.state ∧
      upgradeRelation upgradeProxy wrapperV1.state wrapperV2.state ∧
      ∃ (afterTransferV1 : Benv) (callPreV1 : Devm)
        (spawnV1 : DelegatecallSpawnDescriptor
          (initSevm (outerV1.withBenv afterTransferV1)) callPreV1)
        (routeV1 : OssifiableForwardingRoute outerV1 afterTransferV1
          callPreV1 spawnV1)
        (afterTransferV2 : Benv) (callPreV2 : Devm)
        (spawnV2 : DelegatecallSpawnDescriptor
          (initSevm (outerV2.withBenv afterTransferV2)) callPreV2)
        (routeV2 : OssifiableForwardingRoute outerV2 afterTransferV2
          callPreV2 spawnV2),
        routeV1.transportObligation
            (ScalarInputWord (Bytes.toB256 outerV1.data)) ∧
          routeV2.transportObligation
            (ScalarInputWord (Bytes.toB256 outerV2.data)) ∧
          ExactForwardingContext outerV1 spawnV1 ∧
          ExactForwardingContext outerV2 spawnV2 ∧
          some spawnV1.child.code.toList = Prog.compile v1Prog ∧
          some spawnV2.child.code.toList = Prog.compile v2Prog

/-- The primary migration's initialized R2 state pair refines through two
exact compiled implementation children and the exact compiled proxy wrapper.
-/
theorem throughProxy_primary_refinement
    (proxyProg : Prog) {pre post : State} {call : SharedCall}
    (execution : ExactProxyPairSharedExecution proxyProg pre post call)
    (hInitialized : initializedDomain upgradeProxy post)
    (hRelation : upgradeRelation upgradeProxy pre post) :
    ThroughProxyRefinementResult := by
  rcases execution with
    ⟨proxyExact, outerV1, afterTransferV1, callPreV1, spawnV1,
      routeV1, childV1, implementationV1, tailV1, validV1,
      outerV1Owner, resolvedV1, loadedCodeV1,
      outerV2, afterTransferV2, callPreV2, spawnV2,
      routeV2, childV2, implementationV2, tailV2, validV2,
      outerV2Owner, resolvedV2, loadedCodeV2⟩
  have _proxyExact : proxyProg = runtimeBaseline := proxyExact
  have _validV1 := validV1
  have _validV2 := validV2
  have _resolvedV1 := resolvedV1
  have _resolvedV2 := resolvedV2
  have _loadedCodeV1 := loadedCodeV1
  have _loadedCodeV2 := loadedCodeV2
  have implementationV1Effect := implementationV1.logical_effect
  have implementationV2Effect := implementationV2.logical_effect
  have abstract := behavioral_refinement proxyProg pre post call trivial
    hInitialized hRelation trivial
  have initializedAfter :=
    v2Step_preserves_initializedDomain post call hInitialized
  obtain ⟨outV1, processV1, settledV1⟩ :=
    processMessage_forwardingEnvelope outerV1 afterTransferV1 callPreV1
      spawnV1 routeV1 (.ok childV1) tailV1 implementationV1.certificate
  cases outV1 with
  | error failure =>
      change False at settledV1
      exact settledV1.elim
  | ok wrapperV1 =>
      change ChildToWrapperOkAt outerV1.currentTarget childV1 wrapperV1
        at settledV1
      obtain ⟨outV2, processV2, settledV2⟩ :=
        processMessage_forwardingEnvelope outerV2 afterTransferV2 callPreV2
          spawnV2 routeV2 (.ok childV2) tailV2 implementationV2.certificate
      cases outV2 with
      | error failure =>
          change False at settledV2
          exact settledV2.elim
      | ok wrapperV2 =>
          change ChildToWrapperOkAt outerV2.currentTarget childV2 wrapperV2
            at settledV2
          have outputEq : wrapperV1.output = wrapperV2.output := by
            calc
              wrapperV1.output = childV1.output := settledV1.output
              _ = (v1Step call pre).2 := implementationV1Effect.1
              _ = (v2Step call post).2 := abstract.1
              _ = childV2.output := implementationV2Effect.1.symm
              _ = wrapperV2.output := settledV2.output.symm
          have wrapperInitialized :
              initializedDomain upgradeProxy wrapperV2.state := by
            unfold initializedDomain storageWord
            calc
              (wrapperV2.state.get upgradeProxy).stor.get
                  migrationMarkerSlot =
                  (childV2.state.get upgradeProxy).stor.get
                    migrationMarkerSlot := by
                rw [← outerV2Owner]
                exact (settledV2.storage migrationMarkerSlot).symm
              _ = ((v2Step call post).1.get upgradeProxy).stor.get
                    migrationMarkerSlot :=
                implementationV2Effect.2 migrationMarkerSlot
              _ = migrationMarkerValue := initializedAfter
          have wrapperRelation :
              upgradeRelation upgradeProxy wrapperV1.state
                wrapperV2.state := by
            unfold upgradeRelation storageWord
            calc
              (wrapperV1.state.get upgradeProxy).stor.get v1ValueSlot =
                  (childV1.state.get upgradeProxy).stor.get
                    v1ValueSlot := by
                rw [← outerV1Owner]
                exact (settledV1.storage v1ValueSlot).symm
              _ = ((v1Step call pre).1.get upgradeProxy).stor.get
                    v1ValueSlot :=
                implementationV1Effect.2 v1ValueSlot
              _ = ((v2Step call post).1.get upgradeProxy).stor.get
                    v2ValueSlot := abstract.2
              _ = (childV2.state.get upgradeProxy).stor.get
                    v2ValueSlot :=
                (implementationV2Effect.2 v2ValueSlot).symm
              _ = (wrapperV2.state.get upgradeProxy).stor.get
                    v2ValueSlot := by
                rw [← outerV2Owner]
                exact settledV2.storage v2ValueSlot
          refine ⟨outerV1, outerV2, wrapperV1, wrapperV2,
            processV1, processV2, outputEq, wrapperInitialized,
            wrapperRelation, afterTransferV1, callPreV1, spawnV1, routeV1,
            afterTransferV2, callPreV2, spawnV2, routeV2,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact routeV1.scalarInputWord_transport _
          · exact routeV2.scalarInputWord_transport _
          · exact routeV1.childContext
          · exact routeV2.childContext
          · exact implementationV1.compiled_bytes
          · exact implementationV2.compiled_bytes

/-- The same compiled through-proxy result for an identity application-state
route.  R2 is available only after the explicit identity-admissibility and
three preserved-word premises establish the initialized post-domain. -/
theorem throughProxy_identity_refinement_of_admissible
    (proxyProg : Prog) {pre post : State} {call : SharedCall}
    (execution : ExactProxyPairSharedExecution proxyProg pre post call)
    (admissible : identityAdmissible upgradeProxy pre)
    (s1 : storageWord post upgradeProxy v1ValueSlot =
      storageWord pre upgradeProxy v1ValueSlot)
    (s2 : storageWord post upgradeProxy v2ValueSlot =
      storageWord pre upgradeProxy v2ValueSlot)
    (marker : storageWord post upgradeProxy migrationMarkerSlot =
      storageWord pre upgradeProxy migrationMarkerSlot) :
    ThroughProxyRefinementResult := by
  have sound := upgradeTo_identity_sound_of_admissible admissible s1 s2 marker
  exact throughProxy_primary_refinement proxyProg execution sound.1 sound.2

/-! ## Closed satisfiability witness

The public refinement theorem above intentionally accepts exact forwarding
certificates as premises.  The following closed fixture constructs those
certificates for `value()` on both sides of the migration.  This prevents the
product theorem from being usable only under an uninhabited execution package.
-/

/-- The exact post-migration world used by the closed forwarding witness. -/
def fixtureMigratedState : State :=
  migration upgradeProxy
    (fixturePrestate.setStorVal upgradeProxy implementationSlotLit
      v2Implementation.toB256)

private def sharedValueMessage (state : State) : Msg :=
  { (default : Msg) with
    benv :=
      { fixtureBenv with
        state := state
        stat := { fixtureBenv.stat with origState := state } }
    caller := upgradeAdmin
    target := some upgradeProxy
    currentTarget := upgradeProxy
    gas := 5000000
    value := 0
    data := valueCalldata
    codeAddress := some upgradeProxy
    code := runtimeBaselineCode
    depth := 1024
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := true }

private def sharedValueAfterTransfer (state : State) : Benv :=
  let outer := sharedValueMessage state
  (outer.benv.withState
      (outer.benv.state.setBal outer.caller
        (outer.benv.state.bal outer.caller - outer.value))).addBal
    outer.currentTarget outer.value

private theorem sharedValueMessage_transfer (state : State) :
    (sharedValueMessage state).benvAfterTransfer =
      .ok (sharedValueAfterTransfer state) := by
  unfold Msg.benvAfterTransfer sharedValueAfterTransfer
  simp only [sharedValueMessage, if_true, Benv.subBal, State.subBal]
  rw [if_neg]
  · rfl
  · intro insufficient
    rw [B256.lt_iff_toNat_lt_toNat] at insufficient
    change (state.bal upgradeAdmin).toNat < 0 at insufficient
    exact Nat.not_lt_zero _ insufficient

private theorem sharedValueAfterTransfer_stor
    (state : State) (address : Adr) :
    ((sharedValueAfterTransfer state).state.get address).stor =
      (state.get address).stor := by
  unfold sharedValueAfterTransfer
  change ((((state.setBal upgradeAdmin (state.bal upgradeAdmin - 0)).addBal
    upgradeProxy 0).get address).stor) = _
  unfold State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]

private theorem sharedValueAfterTransfer_code
    (state : State) (address : Adr) :
    (sharedValueAfterTransfer state).state.getCode address =
      state.getCode address := by
  unfold sharedValueAfterTransfer
  change ((state.setBal upgradeAdmin (state.bal upgradeAdmin - 0)).addBal
    upgradeProxy 0).getCode address = _
  rw [State.addBal_getCode, State.setBal_getCode]

private theorem sharedValuePrefixCost (state : State) :
    ossifiableFallbackPrefixCost
      (initSevm (sharedValueMessage state))
      (ossifiableRuntimeFallbackEntry (sharedValueMessage state)
        (sharedValueAfterTransfer state) 4999825) = 2128 := by
  let sevm := initSevm (sharedValueMessage state)
  let entry := ossifiableRuntimeFallbackEntry (sharedValueMessage state)
    (sharedValueAfterTransfer state) 4999825
  have dataLength : sevm.data.length = 4 := by rfl
  have copyCost : ossifiableFallbackCopyCost sevm entry = 9 := by
    unfold ossifiableFallbackCopyCost
    rw [dataLength]
    have extension : entry.extCost [(0, 4)] = 3 := by
      dsimp only [entry, ossifiableRuntimeFallbackEntry]
      exact Devm.extCost_of_size (n := 0) rfl (by decide +kernel)
    rw [extension]
    decide
  have cold : ossifiableFallbackSloadCost sevm entry = 2100 := by
    have keys : entry.accessedStorageKeys = .emptyWithCapacity := by rfl
    unfold ossifiableFallbackSloadCost
    rw [keys, if_neg]
    · rfl
    · simp
  change ossifiableFallbackPrefixCost sevm entry = 2128
  unfold ossifiableFallbackPrefixCost
  rw [copyCost, cold]
  decide +kernel

private def sharedValuePrefixBudget (state : State) :
    OssifiableFallbackPrefixBudget
      (initSevm (sharedValueMessage state))
      (ossifiableRuntimeFallbackEntry (sharedValueMessage state)
        (sharedValueAfterTransfer state) 4999825) where
  callGas := 4997697
  dataLength := by
    change valueCalldata.length < 2 ^ 256
    decide
  entryStack := rfl
  gasBudget := by
    rw [sharedValuePrefixCost]
    rfl

private def sharedValueCallPre (state : State) : Devm :=
  (sharedValuePrefixBudget state).callPre

private def sharedValueAfterAccess (state : State)
    (implementation : Adr) : Devm :=
  addAccessedAddress
    ((sharedValueCallPre state).setMach
      ⟨[], (sharedValueCallPre state).memory,
        (sharedValueCallPre state).gasLeft⟩)
    implementation

private theorem sharedValueCallPre_stack
    (state : State) (implementation : Adr)
    (slot : (state.get upgradeProxy).stor.get implementationSlotLit =
      implementation.toB256) :
    (sharedValueCallPre state).stack =
      Nat.toB256 4997697 :: implementation.toB256 :: 0 :: 4 :: 0 :: 0 ::
        [] := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
  rw [show
      (ossifiableRuntimeFallbackEntry (sharedValueMessage state)
        (sharedValueAfterTransfer state) 4999825).getStorVal
          (initSevm (sharedValueMessage state)).currentTarget
          implementationSlotLit = implementation.toB256 by
    change ((sharedValueAfterTransfer state).state.get
      upgradeProxy).stor.get implementationSlotLit = _
    rw [sharedValueAfterTransfer_stor]
    exact slot]
  rfl

private theorem sharedValueCallPre_memory_size (state : State) :
    (sharedValueCallPre state).memory.size = 32 := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
    ossifiableFallbackCopiedMemory ossifiableRuntimeFallbackEntry
  change (Mem.empty.write 0 valueCalldata).size = 32
  rw [show valueCalldata = 0x3f :: [0xa4, 0xf2, 0x45] by rfl,
    Mem.size_write_cons]
  decide

private theorem sharedValueBeforeSload_cold (state : State) :
    (⟨(initSevm (sharedValueMessage state)).currentTarget,
        implementationSlotLit⟩ : Adr × B256) ∉
      (sharedValuePrefixBudget state).beforeSload.accessedStorageKeys := by
  change (upgradeProxy, implementationSlotLit) ∉
    (.emptyWithCapacity : Std.HashSet (Adr × B256))
  simp

private theorem sharedValueCallPre_state (state : State) :
    (sharedValueCallPre state).state =
      (sharedValueAfterTransfer state).state := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
    OssifiableFallbackPrefixBudget.afterSloadBase
  rw [if_neg (sharedValueBeforeSload_cold state)]
  rfl

private theorem sharedValueCallPre_addresses (state : State) :
    (sharedValueCallPre state).accessedAddresses =
      (.emptyWithCapacity : Std.HashSet Adr) := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
    OssifiableFallbackPrefixBudget.afterSloadBase
  rw [if_neg (sharedValueBeforeSload_cold state)]
  rfl

private theorem sharedValueCallPre_keys (state : State) :
    (sharedValueCallPre state).accessedStorageKeys =
      (.emptyWithCapacity : Std.HashSet (Adr × B256)).insert
        (upgradeProxy, implementationSlotLit) := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
    OssifiableFallbackPrefixBudget.afterSloadBase
  rw [if_neg (sharedValueBeforeSload_cold state)]
  rfl

private theorem sharedValueCallPre_gas (state : State) :
    (sharedValueCallPre state).gasLeft = 4997697 := by
  rfl

private theorem sharedValueCallPre_error (state : State) :
    (sharedValueCallPre state).error = none := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
    OssifiableFallbackPrefixBudget.afterSloadBase
  rw [if_neg (sharedValueBeforeSload_cold state)]
  rfl

private theorem sharedValueCallPre_logs (state : State) :
    (sharedValueCallPre state).logs = [] := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
    OssifiableFallbackPrefixBudget.afterSloadBase
  rw [if_neg (sharedValueBeforeSload_cold state)]
  rfl

private theorem sharedValueCallPre_transient (state : State) :
    (sharedValueCallPre state).transientStorage =
      (sharedValueMessage state).tenv.transientStorage := by
  unfold sharedValueCallPre OssifiableFallbackPrefixBudget.callPre
    OssifiableFallbackPrefixBudget.afterSloadBase
  rw [if_neg (sharedValueBeforeSload_cold state)]
  rfl

private theorem sharedValueAfterAccess_code
    (state : State) (implementation : Adr) (code : ByteArray)
    (installed : state.getCode implementation = code) :
    (sharedValueAfterAccess state implementation).getCode implementation =
      code := by
  unfold sharedValueAfterAccess
  rw [addAccessedAddress_getCode, Devm.getCode_setMach]
  change (sharedValueCallPre state).state.getCode implementation = code
  rw [sharedValueCallPre_state, sharedValueAfterTransfer_code]
  exact installed

private theorem sharedValueAfterAccess_gas
    (state : State) (implementation : Adr) :
    (sharedValueAfterAccess state implementation).gasLeft = 4997697 := by
  unfold sharedValueAfterAccess
  rw [addAccessedAddress_gasLeft, Devm.gasLeft_setMach,
    sharedValueCallPre_gas]

private def sharedValueSpawn
    (state : State) (implementation : Adr) (code : ByteArray)
    (slot : (state.get upgradeProxy).stor.get implementationSlotLit =
      implementation.toB256)
    (installed : state.getCode implementation = code)
    (ordinaryCode : getDelegatedCodeAddress code = none)
    (notPrecompile : pragueRules.isPrecomp implementation = false) :
    DelegatecallSpawnDescriptor
      (initSevm ((sharedValueMessage state).withBenv
        (sharedValueAfterTransfer state))) (sharedValueCallPre state) := {
    gasWord := Nat.toB256 4997697
    codeWord := implementation.toB256
    inputOffsetWord := 0
    inputSizeWord := 4
    outputOffsetWord := 0
    outputSizeWord := 0
    stackTail := []
    delegated := false
    resolvedCodeAddress := implementation
    code := code
    delegationGas := 0
    afterAccess := sharedValueAfterAccess state implementation
    extensionCost := 0
    accessCharge := 2600
    callCost := 4919649
    childGas := 4917049
    stackEq := sharedValueCallPre_stack state implementation slot
    extensionEq := by
      simp only [show (0 : B256).toNat = 0 by decide,
        show (4 : B256).toNat = 4 by decide]
      exact Devm.extCost_covered (by
        rw [sharedValueCallPre_memory_size]
        decide)
    delegationEq := by
      simp only [show implementation.toB256.toAdr = implementation by
        exact toAdr_toB256 implementation]
      change accessDelegation
        (sharedValueAfterAccess state implementation) implementation =
          (false, implementation, code, 0,
            sharedValueAfterAccess state implementation)
      unfold accessDelegation
      have codeEq :
          (sharedValueAfterAccess state implementation).state.getCode
              implementation = code :=
        sharedValueAfterAccess_code state implementation code installed
      dsimp only
      rw [codeEq, ordinaryCode]
    accessEq := by
      simp only [show implementation.toB256.toAdr = implementation by
        exact toAdr_toB256 implementation,
        Devm.setMach_accessedAddresses,
        sharedValueCallPre_addresses]
      simp [accessCost, gasColdAccountAccess]
    splitEq := by
      change calculateMsgCallGas 0 4997697
        (sharedValueAfterAccess state implementation).gasLeft 0 2600 =
          (4919649, 4917049)
      rw [sharedValueAfterAccess_gas]
      decide +kernel
    affordable := by
      change 4919649 ≤
        (sharedValueAfterAccess state implementation).gasLeft
      rw [sharedValueAfterAccess_gas]
      decide
    depthHeadroom := by
      change (1024 : Nat) ≠ 0
      decide
    resolvedNotPrecompile := by
      change pragueRules.isPrecomp implementation = false
      exact notPrecompile
  }

private theorem sharedValueSpawn_exists
    (state : State) (implementation : Adr) (code : ByteArray)
    (slot : (state.get upgradeProxy).stor.get implementationSlotLit =
      implementation.toB256)
    (installed : state.getCode implementation = code)
    (ordinaryCode : getDelegatedCodeAddress code = none)
    (notPrecompile : pragueRules.isPrecomp implementation = false) :
    ∃ spawn : DelegatecallSpawnDescriptor
        (initSevm ((sharedValueMessage state).withBenv
          (sharedValueAfterTransfer state))) (sharedValueCallPre state),
      spawn.gasWord = Nat.toB256 4997697 ∧
      spawn.codeWord = implementation.toB256 ∧
      spawn.inputOffsetWord = 0 ∧
      spawn.inputSizeWord = 4 ∧
      spawn.outputOffsetWord = 0 ∧
      spawn.outputSizeWord = 0 ∧
      spawn.stackTail = [] ∧
      spawn.afterAccess = sharedValueAfterAccess state implementation ∧
      spawn.callCost = 4919649 ∧
      spawn.extensionCost = 0 ∧
      spawn.childGas = 4917049 ∧
      spawn.code = code ∧
      spawn.resolvedCodeAddress = implementation ∧
      spawn = sharedValueSpawn state implementation code slot installed
        ordinaryCode notPrecompile := by
  exact ⟨sharedValueSpawn state implementation code slot installed
      ordinaryCode notPrecompile,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

private theorem sharedValueRoute_exists
    (state : State) (implementation : Adr) (code : ByteArray)
    (slot : (state.get upgradeProxy).stor.get implementationSlotLit =
      implementation.toB256)
    (installed : state.getCode implementation = code)
    (proxyInstalled : state.getCode upgradeProxy = runtimeBaselineCode)
    (ordinaryCode : getDelegatedCodeAddress code = none)
    (notPrecompile : pragueRules.isPrecomp implementation = false)
    (codeNonempty : code.toList ≠ []) :
    ∃ (spawn : DelegatecallSpawnDescriptor
        (initSevm ((sharedValueMessage state).withBenv
          (sharedValueAfterTransfer state))) (sharedValueCallPre state))
      (route : OssifiableForwardingRoute (sharedValueMessage state)
        (sharedValueAfterTransfer state) (sharedValueCallPre state) spawn),
      route.ValidInstallation ∧
        spawn.resolvedCodeAddress = implementation ∧
        spawn.code = code ∧
        spawn = sharedValueSpawn state implementation code slot installed
          ordinaryCode notPrecompile := by
  obtain ⟨spawn, gasWord, codeWord, inputOffset, inputSize,
      outputOffset, outputSize, stackTail, afterAccess, callCost,
      extensionCost, childGas, spawnCode, resolved, spawnExact⟩ :=
    sharedValueSpawn_exists state implementation code slot installed
      ordinaryCode notPrecompile
  have parentMemory : spawn.parent.memory =
      (sharedValueCallPre state).memory := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_memory,
      spawn.afterAccess_memory]
    exact Mem.extends_covered (by
      rw [inputOffset, inputSize, outputOffset, outputSize,
        sharedValueCallPre_memory_size]
      decide)
  have childData : spawn.child.data = valueCalldata := by
    rw [spawn.child_data, inputOffset, inputSize,
      show (0 : B256).toNat = 0 by decide,
      show (4 : B256).toNat = 4 by decide, parentMemory]
    change (((Mem.empty.write 0 valueCalldata).read 0 4).1) =
      valueCalldata
    rw [show 4 = valueCalldata.length by rfl]
    exact Mem.read_write_zero _ (by decide +kernel)
  have parentStack : spawn.parent.stack = [] := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_stack,
      afterAccess]
    rfl
  have parentState : spawn.parent.state =
      (sharedValueAfterTransfer state).state := by
    rw [DelegatecallSpawnDescriptor.parent]
    change spawn.afterAccess.state = _
    rw [afterAccess]
    unfold sharedValueAfterAccess
    change (sharedValueCallPre state).state = _
    exact sharedValueCallPre_state state
  have parentError : spawn.parent.error = none := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_error,
      afterAccess]
    unfold sharedValueAfterAccess
    change (sharedValueCallPre state).error = none
    exact sharedValueCallPre_error state
  have parentLogs : spawn.parent.logs = [] := by
    rw [DelegatecallSpawnDescriptor.parent, afterAccess]
    unfold sharedValueAfterAccess
    change (sharedValueCallPre state).logs = []
    exact sharedValueCallPre_logs state
  have parentTransient : MessageTransientEqualAt upgradeProxy
      spawn.parent.transientStorage
      (sharedValueMessage state).tenv.transientStorage := by
    intro key
    rw [DelegatecallSpawnDescriptor.parent, afterAccess]
    unfold sharedValueAfterAccess
    change ((sharedValueCallPre state).transientStorage.getD upgradeProxy
      Stor.empty).get key = _
    rw [sharedValueCallPre_transient]
  let route : OssifiableForwardingRoute (sharedValueMessage state)
      (sharedValueAfterTransfer state) (sharedValueCallPre state) spawn := {
    transfer := sharedValueMessage_transfer state
    target := rfl
    codeAddress := rfl
    proxyNotPrecompile := by
      change ¬pragueRules.isPrecomp upgradeProxy
      decide +kernel
    runtimeInstalled := rfl
    runtimeCodeLink := by
      change runtimeBaselineCode = state.getCode upgradeProxy
      exact proxyInstalled.symm
    selectorMiss := by
      intro selector member equal
      have selected : Sevm.selector
          (initSevm ((sharedValueMessage state).withBenv
            (sharedValueAfterTransfer state))) = valueSelector := by
        apply selector_of_valueCalldata
        rfl
      have valueMember : valueSelector ∈ runtimeSelectors := by
        rw [← selected, ← equal]
        exact member
      exact (upgradeWitnessSelectors_disjoint_proxy_surface valueSelector
        (by simp [upgradeWitnessSelectors])) valueMember
    implementationSlotWord := by
      rw [codeWord, ← implementationSlotLit_eq_slot,
        sharedValueAfterTransfer_stor]
      exact slot
    descriptorCode := by
      rw [spawnCode, resolved, sharedValueAfterTransfer_code]
      exact installed.symm
    inputOffset := inputOffset
    inputSize := by
      rw [inputSize]
      change (4 : B256).toNat = valueCalldata.length
      rfl
    outputOffset := outputOffset
    outputSize := outputSize
    emptyTail := stackTail
    childData := childData
    afterTransferStat := rfl
    parentStackRoom := by rw [parentStack]; decide
    parentError := parentError
    parentLogs := parentLogs
    parentStorage := by
      intro key
      rw [parentState, sharedValueAfterTransfer_stor]
      rfl
    parentTransient := parentTransient
    fallbackGas := 4999825
    entryGas := by
      change 5000000 = 4999825 +
        linearDispatchFallbackCost runtimeBaselineEntries + fsigCost +
          gJumpdest
      decide +kernel
    prefixBudget := sharedValuePrefixBudget state
    callPreEq := rfl
    compileLink := by
      change some runtimeBaselineCode.toList = Prog.compile runtimeBaseline
      rw [runtimeBaseline_compile]
      simp [runtimeBaselineCode, ByteArray.toList_eq_toList_data]
  }
  have valid : route.ValidInstallation := {
    canonicalSlotWord := by
      rw [codeWord, toAdr_toB256]
    executedCodeNonempty := by
      rw [spawnCode]
      exact codeNonempty
  }
  exact ⟨spawn, route, valid, resolved, spawnCode, spawnExact⟩

private theorem fixturePrestate_implementation :
    (fixturePrestate.get upgradeProxy).stor.get implementationSlotLit =
      v1Implementation.toB256 := by
  unfold fixturePrestate fixtureProxyStorage
  rw [State.get_set_self,
    Stor.get_set_ne _ (show v1ValueSlot ≠ implementationSlotLit by decide),
    Stor.get_set_ne _ (show adminSlotLit ≠ implementationSlotLit by decide),
    Stor.get_set_self]

private theorem fixtureMigratedState_implementation :
    (fixtureMigratedState.get upgradeProxy).stor.get implementationSlotLit =
      v2Implementation.toB256 := by
  change storageWord fixtureMigratedState upgradeProxy
    implementationSlotLit = v2Implementation.toB256
  unfold fixtureMigratedState migration
  rw [storageWord_setStorVal_ne _ _ migrationMarkerSlot
      implementationSlotLit migrationMarkerValue (by decide),
    storageWord_setStorVal_ne _ _ v2ValueSlot implementationSlotLit _
      (by decide),
    storageWord_setStorVal_self]

private theorem State.setStorVal_getCode_local
    (state : State) (owner address : Adr) (slot value : B256) :
    (state.setStorVal owner slot value).getCode address =
      state.getCode address := by
  change ((state.setStorVal owner slot value).get address).code =
    (state.get address).code
  unfold State.setStorVal
  by_cases equal : owner = address
  · subst address
    rw [State.get_set_self]
  · rw [State.get_set_ne _ equal]

private theorem fixturePrestate_v1Code :
    fixturePrestate.getCode v1Implementation = v1Code := by
  change (fixturePrestate.get v1Implementation).code = v1Code
  unfold fixturePrestate
  rw [State.get_set_ne _
      (show upgradeProxy ≠ v1Implementation by decide),
    State.get_set_ne _
      (show v2Implementation ≠ v1Implementation by decide),
    State.get_set_self]

private theorem fixtureMigratedState_v2Code :
    fixtureMigratedState.getCode v2Implementation = v2Code := by
  unfold fixtureMigratedState migration
  repeat' rw [State.setStorVal_getCode_local]
  change (fixturePrestate.get v2Implementation).code = v2Code
  unfold fixturePrestate
  rw [State.get_set_ne _
      (show upgradeProxy ≠ v2Implementation by decide),
    State.get_set_self]

private theorem fixturePrestate_proxyCode :
    fixturePrestate.getCode upgradeProxy = runtimeBaselineCode := by
  change (fixturePrestate.get upgradeProxy).code = runtimeBaselineCode
  unfold fixturePrestate
  rw [State.get_set_self]

private theorem fixtureMigratedState_proxyCode :
    fixtureMigratedState.getCode upgradeProxy = runtimeBaselineCode := by
  unfold fixtureMigratedState migration
  repeat' rw [State.setStorVal_getCode_local]
  exact fixturePrestate_proxyCode

private theorem v1Code_ordinary : getDelegatedCodeAddress v1Code = none := by
  decide +kernel

private theorem v2Code_ordinary : getDelegatedCodeAddress v2Code = none := by
  decide +kernel

private theorem v1Code_nonempty : v1Code.toList ≠ [] := by
  intro empty
  have lengthEq := congrArg List.length empty
  rw [v1Code_toList, v1Bytes_length] at lengthEq
  contradiction

private theorem v2Code_nonempty : v2Code.toList ≠ [] := by
  intro empty
  have lengthEq := congrArg List.length empty
  rw [v2Code_toList, v2Bytes_length] at lengthEq
  contradiction

private theorem v1Implementation_notPrecompile :
    pragueRules.isPrecomp v1Implementation = false := by
  decide +kernel

private theorem v2Implementation_notPrecompile :
    pragueRules.isPrecomp v2Implementation = false := by
  decide +kernel

private def v1ValueSpawn : DelegatecallSpawnDescriptor
    (initSevm ((sharedValueMessage fixturePrestate).withBenv
      (sharedValueAfterTransfer fixturePrestate)))
    (sharedValueCallPre fixturePrestate) :=
  sharedValueSpawn fixturePrestate v1Implementation v1Code
    fixturePrestate_implementation fixturePrestate_v1Code v1Code_ordinary
      v1Implementation_notPrecompile

private def v2ValueSpawn : DelegatecallSpawnDescriptor
    (initSevm ((sharedValueMessage fixtureMigratedState).withBenv
      (sharedValueAfterTransfer fixtureMigratedState)))
    (sharedValueCallPre fixtureMigratedState) :=
  sharedValueSpawn fixtureMigratedState v2Implementation v2Code
    fixtureMigratedState_implementation fixtureMigratedState_v2Code
      v2Code_ordinary v2Implementation_notPrecompile

/-- The actual v1 child spawned by the closed `value()` proxy route. -/
def fixtureV1ValueChildMessage : Msg := v1ValueSpawn.child

/-- The actual initialized-v2 child spawned by the closed `value()` route. -/
def fixtureV2ValueChildMessage : Msg := v2ValueSpawn.child

private theorem fixtureV1ValueChild_data :
    fixtureV1ValueChildMessage.data = valueCalldata := by
  obtain ⟨spawn, route, _, _, _, spawnExact⟩ :=
    sharedValueRoute_exists fixturePrestate v1Implementation v1Code
      fixturePrestate_implementation fixturePrestate_v1Code
      fixturePrestate_proxyCode v1Code_ordinary
      v1Implementation_notPrecompile v1Code_nonempty
  subst spawn
  simpa [fixtureV1ValueChildMessage, v1ValueSpawn,
    sharedValueMessage] using route.childData

private theorem fixtureV2ValueChild_data :
    fixtureV2ValueChildMessage.data = valueCalldata := by
  obtain ⟨spawn, route, _, _, _, spawnExact⟩ :=
    sharedValueRoute_exists fixtureMigratedState v2Implementation v2Code
      fixtureMigratedState_implementation fixtureMigratedState_v2Code
      fixtureMigratedState_proxyCode v2Code_ordinary
      v2Implementation_notPrecompile v2Code_nonempty
  subst spawn
  simpa [fixtureV2ValueChildMessage, v2ValueSpawn,
    sharedValueMessage] using route.childData

private theorem fixtureV1ValueChild_initialMemory :
    (initDevm fixtureV1ValueChildMessage).memory = Mem.empty := by
  rfl

private theorem fixtureV2ValueChild_initialMemory :
    (initDevm fixtureV2ValueChildMessage).memory = Mem.empty := by
  rfl

private theorem fixtureV1ValueChild_initialStack :
    (initDevm fixtureV1ValueChildMessage).stack = [] := by
  rfl

private theorem fixtureV2ValueChild_initialStack :
    (initDevm fixtureV2ValueChildMessage).stack = [] := by
  rfl

private theorem fixtureV1ValueChild_currentTarget :
    (initSevm fixtureV1ValueChildMessage).currentTarget = upgradeProxy := by
  rfl

private theorem fixtureV2ValueChild_currentTarget :
    (initSevm fixtureV2ValueChildMessage).currentTarget = upgradeProxy := by
  rfl

private theorem fixtureV1ValueChild_initialKeys :
    (initDevm fixtureV1ValueChildMessage).accessedStorageKeys =
      (.emptyWithCapacity : Std.HashSet (Adr × B256)).insert
        (upgradeProxy, implementationSlotLit) := by
  change (sharedValueAfterAccess fixturePrestate
    v1Implementation).accessedStorageKeys = _
  unfold sharedValueAfterAccess
  change (sharedValueCallPre fixturePrestate).accessedStorageKeys = _
  exact sharedValueCallPre_keys fixturePrestate

private theorem fixtureV2ValueChild_initialKeys :
    (initDevm fixtureV2ValueChildMessage).accessedStorageKeys =
      (.emptyWithCapacity : Std.HashSet (Adr × B256)).insert
        (upgradeProxy, implementationSlotLit) := by
  change (sharedValueAfterAccess fixtureMigratedState
    v2Implementation).accessedStorageKeys = _
  unfold sharedValueAfterAccess
  change (sharedValueCallPre fixtureMigratedState).accessedStorageKeys = _
  exact sharedValueCallPre_keys fixtureMigratedState

private theorem fixtureV1ValueChild_value :
    (initDevm fixtureV1ValueChildMessage).getStorVal upgradeProxy
      v1ValueSlot = 42 := by
  change (v1ValueSpawn.parent.state.get upgradeProxy).stor.get
    v1ValueSlot = 42
  change ((sharedValueAfterAccess fixturePrestate
    v1Implementation).state.get upgradeProxy).stor.get v1ValueSlot = 42
  unfold sharedValueAfterAccess
  change ((sharedValueCallPre fixturePrestate).state.get
    upgradeProxy).stor.get v1ValueSlot = 42
  rw [sharedValueCallPre_state]
  rw [sharedValueAfterTransfer_stor]
  unfold fixturePrestate fixtureProxyStorage
  rw [State.get_set_self, Stor.get_set_self]

private theorem fixtureV2ValueChild_value :
    (initDevm fixtureV2ValueChildMessage).getStorVal upgradeProxy
      v2ValueSlot = 42 := by
  change (v2ValueSpawn.parent.state.get upgradeProxy).stor.get
    v2ValueSlot = 42
  change ((sharedValueAfterAccess fixtureMigratedState
    v2Implementation).state.get upgradeProxy).stor.get v2ValueSlot = 42
  unfold sharedValueAfterAccess
  change ((sharedValueCallPre fixtureMigratedState).state.get
    upgradeProxy).stor.get v2ValueSlot = 42
  rw [sharedValueCallPre_state, sharedValueAfterTransfer_stor]
  change storageWord fixtureMigratedState upgradeProxy v2ValueSlot = 42
  unfold fixtureMigratedState
  rw [migration_writes_v2]
  rw [storageWord_setStorVal_ne _ _ implementationSlotLit v1ValueSlot _
      (by decide)]
  change (fixturePrestate.get upgradeProxy).stor.get v1ValueSlot = 42
  unfold fixturePrestate fixtureProxyStorage
  rw [State.get_set_self, Stor.get_set_self]

private theorem fsig_prepend_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (selector : B256) (memory : Mem) (gas : Nat)
    (tail : Func) (post : Devm)
    (selectorEq : Sevm.selector sevm = selector)
    (body : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], memory, gas⟩) tail (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, gas + 11⟩) (fsig +++ tail)
      (.ok post) := by
  unfold fsig cdl shiftRight
  func_run (4) [selector]
  case a => exact body

private theorem fixtureV1ValueChild_run :
    ∃ child,
      Prog.RunCompiledTo (initSevm fixtureV1ValueChildMessage)
        (initDevm fixtureV1ValueChildMessage) v1Prog (.ok child) ∧
      child.error = none ∧
      child.output = (42 : B256).toBytes ∧
      child.gasLeft = 4914877 := by
  have slotCold :
      ((initSevm fixtureV1ValueChildMessage).currentTarget,
        v1ValueSlot) ∉
        (initDevm fixtureV1ValueChildMessage).accessedStorageKeys := by
    rw [fixtureV1ValueChild_currentTarget,
      fixtureV1ValueChild_initialKeys]
    simp [show implementationSlotLit ≠ v1ValueSlot by decide]
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Prog.runCompiledTo_intro (G := 4917048)
    · rfl
    · rfl
    · unfold v1Prog
      apply fsig_prepend_runCompiledTo
        (base := initDevm fixtureV1ValueChildMessage)
        (selector := valueSelector)
        (memory := (initDevm fixtureV1ValueChildMessage).memory)
        (gas := 4917037)
      · apply selector_of_valueCalldata
        simpa [initSevm] using fixtureV1ValueChild_data
      · unfold v1Entries linearDispatchWith nonpayable loadScalar mstoreAt
        func_run [1, 1, 3]
        all_goals try
          norm_num [Devm.gasLeft_setMach, gBase, gVerylow, gHigh,
            gJumpdest, gasColdSload]
        case h_ext => decide
        case a =>
          apply Func.runCompiledTo_ret_word
            (i := 0) (sz := 32) (s := []) (e := 0) (G := 4914877)
            (out := (42 : B256).toBytes)
          · rfl
          · apply Devm.extCost_covered
            rfl
          · simp only [Devm.gasLeft_setMach]
          · apply Devm.memRead_word_fst
            change Mem.empty.write 0
                ((initDevm fixtureV1ValueChildMessage).getStorVal
                  upgradeProxy v1ValueSlot).toBytes =
              Mem.empty.write 0 (42 : B256).toBytes
            rw [fixtureV1ValueChild_value]
  · rfl
  · rfl
  · rfl

private theorem fixtureV2ValueChild_run :
    ∃ child,
      Prog.RunCompiledTo (initSevm fixtureV2ValueChildMessage)
        (initDevm fixtureV2ValueChildMessage) v2Prog (.ok child) ∧
      child.error = none ∧
      child.output = (42 : B256).toBytes ∧
      child.gasLeft = 4914877 := by
  have slotCold :
      ((initSevm fixtureV2ValueChildMessage).currentTarget,
        v2ValueSlot) ∉
        (initDevm fixtureV2ValueChildMessage).accessedStorageKeys := by
    rw [fixtureV2ValueChild_currentTarget,
      fixtureV2ValueChild_initialKeys]
    simp [show implementationSlotLit ≠ v2ValueSlot by decide]
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Prog.runCompiledTo_intro (G := 4917048)
    · rfl
    · rfl
    · unfold v2Prog
      apply fsig_prepend_runCompiledTo
        (base := initDevm fixtureV2ValueChildMessage)
        (selector := valueSelector)
        (memory := (initDevm fixtureV2ValueChildMessage).memory)
        (gas := 4917037)
      · apply selector_of_valueCalldata
        simpa [initSevm] using fixtureV2ValueChild_data
      · unfold v2Entries linearDispatchWith nonpayable loadScalar mstoreAt
        func_run [1, 1, 3]
        all_goals try
          norm_num [Devm.gasLeft_setMach, gBase, gVerylow, gHigh,
            gJumpdest, gasColdSload]
        case h_ext => decide
        case a =>
          apply Func.runCompiledTo_ret_word
            (i := 0) (sz := 32) (s := []) (e := 0) (G := 4914877)
            (out := (42 : B256).toBytes)
          · rfl
          · apply Devm.extCost_covered
            rfl
          · simp only [Devm.gasLeft_setMach]
          · apply Devm.memRead_word_fst
            change Mem.empty.write 0
                ((initDevm fixtureV2ValueChildMessage).getStorVal
                  upgradeProxy v2ValueSlot).toBytes =
              Mem.empty.write 0 (42 : B256).toBytes
            rw [fixtureV2ValueChild_value]
  · rfl
  · rfl
  · rfl

private theorem fixtureV1ValueChild_compiled :
    some (initSevm fixtureV1ValueChildMessage).code.toList =
      Prog.compile v1Prog := by
  change some v1ValueSpawn.child.code.toList = Prog.compile v1Prog
  rw [DelegatecallSpawnDescriptor.child_code]
  change some v1Code.toList = Prog.compile v1Prog
  rw [v1Code_toList, v1Prog_compile]

private theorem fixtureV2ValueChild_compiled :
    some (initSevm fixtureV2ValueChildMessage).code.toList =
      Prog.compile v2Prog := by
  change some v2ValueSpawn.child.code.toList = Prog.compile v2Prog
  rw [DelegatecallSpawnDescriptor.child_code]
  change some v2Code.toList = Prog.compile v2Prog
  rw [v2Code_toList, v2Prog_compile]

private theorem fixtureV1ValueChild_initialStorage :
    MessageStorageEqualAt upgradeProxy
      fixtureV1ValueChildMessage.benv.state fixturePrestate := by
  intro key
  change (v1ValueSpawn.parent.state.get upgradeProxy).stor.get key = _
  change ((sharedValueAfterAccess fixturePrestate
    v1Implementation).state.get upgradeProxy).stor.get key = _
  unfold sharedValueAfterAccess
  change ((sharedValueCallPre fixturePrestate).state.get
    upgradeProxy).stor.get key = _
  rw [sharedValueCallPre_state, sharedValueAfterTransfer_stor]

private theorem fixtureV2ValueChild_initialStorage :
    MessageStorageEqualAt upgradeProxy
      fixtureV2ValueChildMessage.benv.state fixtureMigratedState := by
  intro key
  change (v2ValueSpawn.parent.state.get upgradeProxy).stor.get key = _
  change ((sharedValueAfterAccess fixtureMigratedState
    v2Implementation).state.get upgradeProxy).stor.get key = _
  unfold sharedValueAfterAccess
  change ((sharedValueCallPre fixtureMigratedState).state.get
    upgradeProxy).stor.get key = _
  rw [sharedValueCallPre_state, sharedValueAfterTransfer_stor]

private theorem v1ValueSpawn_parentMemorySize :
    v1ValueSpawn.parent.memory.size = 32 := by
  rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_memory,
    v1ValueSpawn.afterAccess_memory]
  change ((sharedValueCallPre fixturePrestate).memory.extends
    [(0, 4), (0, 0)]).size = 32
  rw [Mem.extends_covered (by
    rw [sharedValueCallPre_memory_size]
    decide), sharedValueCallPre_memory_size]

private theorem v2ValueSpawn_parentMemorySize :
    v2ValueSpawn.parent.memory.size = 32 := by
  rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_memory,
    v2ValueSpawn.afterAccess_memory]
  change ((sharedValueCallPre fixtureMigratedState).memory.extends
    [(0, 4), (0, 0)]).size = 32
  rw [Mem.extends_covered (by
    rw [sharedValueCallPre_memory_size]
    decide), sharedValueCallPre_memory_size]

private theorem v1ValueSpawn_parentStack :
    v1ValueSpawn.parent.stack = [] := by
  rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_stack]
  rfl

private theorem v2ValueSpawn_parentStack :
    v2ValueSpawn.parent.stack = [] := by
  rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_stack]
  rfl

private theorem v1ValueSpawn_parentGas :
    v1ValueSpawn.parent.gasLeft = 78048 := by
  rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_gasLeft]
  change (sharedValueAfterAccess fixturePrestate
    v1Implementation).gasLeft - (4919649 + 0) = 78048
  rw [sharedValueAfterAccess_gas]

private theorem v2ValueSpawn_parentGas :
    v2ValueSpawn.parent.gasLeft = 78048 := by
  rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_gasLeft]
  change (sharedValueAfterAccess fixtureMigratedState
    v2Implementation).gasLeft - (4919649 + 0) = 78048
  rw [sharedValueAfterAccess_gas]

private noncomputable def delegatedChildCertificate_of_run
    {sevm : Sevm} {callPre : Devm}
    (spawn : DelegatecallSpawnDescriptor sevm callPre)
    {program : Prog} {child : Devm}
    (run : Prog.RunCompiledTo (initSevm spawn.child)
      (initDevm spawn.child) program (.ok child))
    (compiled : some (initSevm spawn.child).code.toList =
      Prog.compile program)
    (clean : child.error = none) :
    DelegatedChildCertificate spawn.child (.ok child) := by
  have raw : exec (initEvm spawn.child) = .ok child := by
    simpa [initEvm] using Prog.exec_of_runCompiledTo run compiled
  have process : processMessage spawn.child = .ok child := by
    rw [MessageExecution.processMessage_eq_settle_exec_of_enter
      spawn.child (initEvm spawn.child) spawn.crossing.1, raw]
    simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle,
      show child.error.isSome = false by rw [clean]; rfl]
  let trace := Classical.choice
    (ExecutionTrace.exists_processMessageTrace spawn.child (.ok child)
      process)
  exact ⟨trace⟩

private def closedValueTailBudget
    {sevm : Sevm} {callPre : Devm}
    (spawn : DelegatecallSpawnDescriptor sevm callPre) (child : Devm)
    (outputSize : spawn.outputSizeWord = 0)
    (parentMemory : spawn.parent.memory.size = 32)
    (parentStack : spawn.parent.stack = [])
    (parentGas : spawn.parent.gasLeft = 78048)
    (clean : child.error = none)
    (output : child.output = (42 : B256).toBytes)
    (childGas : child.gasLeft = 4914877) :
    ForwardingTailBudget spawn child := by
  have outputSizeNat : spawn.outputSizeWord.toNat = 0 := by
    rw [outputSize]
    rfl
  have resumeMemory :
      (forwardingCleanResume spawn child).memory.size = 32 := by
    unfold forwardingCleanResume
    rw [outputSizeNat, List.take_zero, Devm.memWrite_nil,
      Devm.memory_setMach, parentMemory]
  have resumeGas :
      (forwardingCleanResume spawn child).gasLeft = 4992925 := by
    unfold forwardingCleanResume
    rw [outputSizeNat, List.take_zero, Devm.memWrite_nil,
      Devm.gasLeft_setMach, parentGas, childGas]
  have tailCost :
      forwardingCleanTailCost (forwardingCleanResume spawn child) = 33 := by
    have extension :
        (forwardingCleanResume spawn child).extCost [(0, 32)] = 0 := by
      have covered : memExtsSize
          (forwardingCleanResume spawn child).memory.size [(0, 32)] =
          (forwardingCleanResume spawn child).memory.size := by
        rw [resumeMemory]
        decide
      exact Devm.extCost_covered covered
    have wordLength : (42 : B256).toBytes.length = 32 := by decide
    unfold forwardingCleanTailCost
    rw [forwardingCleanResume_returnData, output, wordLength, extension]
    decide
  refine ForwardingTailBudget.clean ?_ ?_ ?_ ?_ 4992892 ?_
  · rw [clean]
    rfl
  · rw [output]
    decide
  · rw [resumeMemory]
  · rw [parentStack]
    decide
  · rw [resumeGas, tailCost]

/-- A closed inhabitant of the full exact forwarding package for `value()`.
Both delegated children are the descriptors' actual spawned messages, and
both certificates come from the compiled v1/v2 walks above. -/
theorem fixture_exactProxyPairSharedExecution_value :
    ExactProxyPairSharedExecution runtimeBaseline fixturePrestate
      fixtureMigratedState .value := by
  obtain ⟨childV1, runV1, errorV1, outputV1, gasV1⟩ :=
    fixtureV1ValueChild_run
  obtain ⟨childV2, runV2, errorV2, outputV2, gasV2⟩ :=
    fixtureV2ValueChild_run
  obtain ⟨spawnV1, routeV1, validV1, resolvedV1, codeV1,
      spawnExactV1⟩ :=
    sharedValueRoute_exists fixturePrestate v1Implementation v1Code
      fixturePrestate_implementation fixturePrestate_v1Code
      fixturePrestate_proxyCode v1Code_ordinary
      v1Implementation_notPrecompile v1Code_nonempty
  subst spawnV1
  obtain ⟨spawnV2, routeV2, validV2, resolvedV2, codeV2,
      spawnExactV2⟩ :=
    sharedValueRoute_exists fixtureMigratedState v2Implementation v2Code
      fixtureMigratedState_implementation fixtureMigratedState_v2Code
      fixtureMigratedState_proxyCode v2Code_ordinary
      v2Implementation_notPrecompile v2Code_nonempty
  subst spawnV2
  have implementationV1 : V1SharedChildExecution v1ValueSpawn.child
      fixturePrestate .value childV1 := {
    code := by
      rw [DelegatecallSpawnDescriptor.child_code]
      rfl
    data := by
      simpa [v1ValueSpawn, sharedCalldata, sharedValueMessage] using
        routeV1.childData
    owner := by rfl
    initialStorage := fixtureV1ValueChild_initialStorage
    run := by simpa [fixtureV1ValueChildMessage] using runV1
    certificate := delegatedChildCertificate_of_run v1ValueSpawn
      (by simpa [fixtureV1ValueChildMessage] using runV1)
      (by simpa [fixtureV1ValueChildMessage] using
        fixtureV1ValueChild_compiled)
      errorV1
    clean := by rw [errorV1]; rfl
  }
  have implementationV2 : V2SharedChildExecution v2ValueSpawn.child
      fixtureMigratedState .value childV2 := {
    code := by
      rw [DelegatecallSpawnDescriptor.child_code]
      rfl
    data := by
      simpa [v2ValueSpawn, sharedCalldata, sharedValueMessage] using
        routeV2.childData
    owner := by rfl
    initialStorage := fixtureV2ValueChild_initialStorage
    run := by simpa [fixtureV2ValueChildMessage] using runV2
    certificate := delegatedChildCertificate_of_run v2ValueSpawn
      (by simpa [fixtureV2ValueChildMessage] using runV2)
      (by simpa [fixtureV2ValueChildMessage] using
        fixtureV2ValueChild_compiled)
      errorV2
    clean := by rw [errorV2]; rfl
  }
  let tailV1 : ForwardingTailBudget v1ValueSpawn childV1 :=
    closedValueTailBudget v1ValueSpawn childV1 rfl
      v1ValueSpawn_parentMemorySize v1ValueSpawn_parentStack
      v1ValueSpawn_parentGas errorV1 outputV1 gasV1
  let tailV2 : ForwardingTailBudget v2ValueSpawn childV2 :=
    closedValueTailBudget v2ValueSpawn childV2 rfl
      v2ValueSpawn_parentMemorySize v2ValueSpawn_parentStack
      v2ValueSpawn_parentGas errorV2 outputV2 gasV2
  refine ⟨rfl, sharedValueMessage fixturePrestate,
    sharedValueAfterTransfer fixturePrestate,
    sharedValueCallPre fixturePrestate, v1ValueSpawn, routeV1,
    childV1, implementationV1, tailV1, validV1, rfl, resolvedV1,
    codeV1, sharedValueMessage fixtureMigratedState,
    sharedValueAfterTransfer fixtureMigratedState,
    sharedValueCallPre fixtureMigratedState, v2ValueSpawn, routeV2,
    childV2, implementationV2, tailV2, validV2, rfl, resolvedV2,
    codeV2⟩

theorem fixtureMigratedState_initialized :
    initializedDomain upgradeProxy fixtureMigratedState := by
  unfold fixtureMigratedState
  exact migration_establishes_initializedDomain upgradeProxy _

theorem fixtureMigratedState_relation :
    upgradeRelation upgradeProxy fixturePrestate fixtureMigratedState := by
  unfold fixtureMigratedState upgradeRelation
  rw [migration_writes_v2]
  rw [storageWord_setStorVal_ne _ _ implementationSlotLit v1ValueSlot _
    (by decide)]

/-- The closed exact pair has a concrete settled through-proxy refinement. -/
theorem fixture_throughProxy_value_refinement :
    ThroughProxyRefinementResult :=
  throughProxy_primary_refinement runtimeBaseline
    fixture_exactProxyPairSharedExecution_value
    fixtureMigratedState_initialized fixtureMigratedState_relation

/-- Direct composition from one exact primary `upgradeToAndCall` execution to
the settled through-proxy refinement theorem.  The initialized-domain and R2
premises are derived from that same primary run, not supplied independently. -/
theorem upgradeToAndCall_primary_throughProxy_refinement
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
    (hchild : PrimaryChildExecution sevm post)
    {call : SharedCall}
    (sharedExecution : ExactProxyPairSharedExecution proxyProg
      entry.state post.state call) :
    ThroughProxyRefinementResult := by
  obtain ⟨_, _, _, _, _, initialized, relation, _⟩ :=
    upgradeToAndCall_primary_realizes_migration proxyProg hproxy houter
      hentryStack hvalue howner hcaller hdata hauthorized hliveAdmin
      hv1Installed hv2Code hrawCommit hentryMemoryWf hentryMemoryReads hchild
  exact throughProxy_primary_refinement proxyProg sharedExecution initialized
    relation


end Blanc.ProxyPair.Upgrade
