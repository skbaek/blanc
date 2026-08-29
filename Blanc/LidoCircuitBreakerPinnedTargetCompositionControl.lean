import Blanc.LidoCircuitBreakerPinnedTargetStubCrossing
import Blanc.LidoCircuitBreakerPublicPauseControl

/-!
# Closed pinned-target public-pause control

This test-scoped world installs the compiled pinned-target stub in the
production CircuitBreaker row-19 public-pause state.  The source-level walk
below is proof evidence; no evaluator result is reflected into a theorem.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- Row 19 with the compiled pinned-target stub installed at the pause target. -/
def stubPauseWorldState : State :=
  State.set
    (State.set (.empty : State) configWorldOwner
      { Acct.nil with stor := pauseLastWorldStor, code := configWorldCode })
    pauseWorldCallee
      { Acct.nil with code := PinnedTargetControl.stubCode }

/-- Ample gas for the production public pause and both compiled-stub calls. -/
def stubPauseWorldGas : Nat := 100000

/-- The row-19 public message with the compiled stub installed. -/
def stubPauseWorldMsg : Msg :=
  { (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas) with
    benv :=
      { (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas).benv with
        state := stubPauseWorldState
        stat :=
          { (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas).benv.stat with
            origState := stubPauseWorldState } } }

def stubPauseWorldSevm : Sevm := initSevm stubPauseWorldMsg

def stubPauseWorldPre : Devm := initDevm stubPauseWorldMsg

theorem stubPauseWorldState_get_breaker :
    stubPauseWorldState.get configWorldOwner =
      { Acct.nil with stor := pauseLastWorldStor, code := configWorldCode } := by
  rw [stubPauseWorldState,
    State.get_set_ne _ pauseWorld_callee_ne_owner, State.get_set_self]

theorem stubPauseWorldState_get_target :
    stubPauseWorldState.get pauseWorldCallee =
      { Acct.nil with code := PinnedTargetControl.stubCode } := by
  rw [stubPauseWorldState, State.get_set_self]

theorem stubPauseWorld_targetCode :
    stubPauseWorldState.getCode pauseWorldCallee =
      PinnedTargetControl.stubCode := by
  show (stubPauseWorldState.get pauseWorldCallee).code = _
  rw [stubPauseWorldState_get_target]

theorem stubPauseWorld_codeBytes :
    stubPauseWorldSevm.code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [stubPauseWorldSevm, stubPauseWorldMsg, initSevm] using
    pauseWorld_msgCode pauseLastWorldStor stubPauseWorldGas

theorem stubPauseWorld_currentTarget :
    stubPauseWorldSevm.currentTarget = configWorldOwner := rfl

theorem stubPauseWorld_callerWord :
    stubPauseWorldSevm.caller.toB256 = pauseWorldPauser :=
  pauseWorld_pauserAdr_toB256

theorem stubPauseWorld_getStorVal {key : B256} :
    stubPauseWorldPre.getStorVal configWorldOwner key =
      pauseLastWorldStor.get key := by
  change (stubPauseWorldState.get configWorldOwner).stor.get key = _
  rw [stubPauseWorldState_get_breaker]

theorem stubPauseWorld_targetCodeAt :
    CodeAt stubPauseWorldPre pauseWorldCallee
      PinnedTargetControl.stubCode := by
  exact stubPauseWorld_targetCode

/-- The installed-stub world satisfies the complete production public-entry
premise bundle, independently of its terminal result. -/
theorem stubPauseWorld_publicPausePremises :
    PublicPauseEntryPremises stubPauseWorldSevm stubPauseWorldPre
      configWorldOwner pauseWorldCallee.toB256 pauseWorldDuration 1 1
      pauseWorldCallee.toB256 [] PinnedTargetControl.stubCode := by
  refine {
    productionBytes := stubPauseWorld_codeBytes
    currentTarget := stubPauseWorld_currentTarget
    codeAddress := rfl
    valueZero := rfl
    dynamic := rfl
    entered := ?_
    image := ?_
    calldata := rfl
    selectorEq := ?_
    targetCanonical := validAdr_toB256 pauseWorldCallee
    targetNonzero := by decide
    callerNonzero := ?_
    unlocked := rfl
    targetCodeAt := ?_
    assigned := ?_
    live := ?_
    durationRead := ?_
    indexRead := ?_
    lengthRead := ?_
    lastRead := ?_
    assignmentCountNe := ?_
    assignmentIndexNe := pauseWorld_assignCallee_ne_indexCallee
    assignmentLengthNe := pauseWorld_length_ne_assignCallee.symm
    assignmentEntryNe := pauseWorld_entryOne_ne_assignCallee.symm
    countRemovedEntryNe := ?_
    countMovedIndexNe := ?_
    countIndexNe := ?_
    countLengthNe := ?_
    countEntryNe := ?_
  }
  · decide
  · unfold MemImage
    exact ⟨Mem.wf_empty, Mem.reads_empty⟩
  · have dataEq : stubPauseWorldSevm.data =
        (pauseWorldSevm pauseLastWorldStor stubPauseWorldGas).data := by
      change stubPauseWorldMsg.data =
        (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas).data
      rfl
    have selectorEq : Sevm.selector stubPauseWorldSevm =
        Sevm.selector
          (pauseWorldSevm pauseLastWorldStor stubPauseWorldGas) := by
      unfold Sevm.selector Sevm.dataWord
      rw [dataEq]
    exact selectorEq.trans
      (pauseWorld_selector pauseLastWorldStor stubPauseWorldGas)
  · rw [stubPauseWorld_callerWord]
    decide
  · rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
      toAdr_toB256 pauseWorldCallee]
    exact stubPauseWorld_targetCodeAt
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_callerWord,
      stubPauseWorld_getStorVal, pauseLastStor_assignment]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_callerWord,
      stubPauseWorld_getStorVal, pauseLastStor_expiry]
    decide
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_duration]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_index]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_length]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_entry]
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_assignCallee_ne_count
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_length_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm

theorem stubPauseWorld_target_ne_owner :
    pauseWorldCallee.toB256.toAdr ≠
      stubPauseWorldSevm.currentTarget := by
  rw [toAdr_toB256, stubPauseWorld_currentTarget]
  exact pauseWorld_callee_ne_owner

private theorem stubPauseWorld_target_not_precompile :
    stubPauseWorldSevm.benvStat.rules.isPrecomp pauseWorldCallee = false := by
  decide +kernel

/-! ## Projection helpers

Small `rfl`-or-split lemmas for reading fields through the tower layers the
composition threads. -/

/-- Both arms of `temporalSloadBase` return the base world with at most the
accessed-key set changed, so the error, output, accessed-address and code
fields all pass through; the named projections below read this one case
split. -/
private theorem temporalSloadBase_carriers (sevm : Sevm) (base : Devm)
    (key : B256) :
    (temporalSloadBase sevm base key).error = base.error ∧
      (temporalSloadBase sevm base key).output = base.output ∧
      (temporalSloadBase sevm base key).accessedAddresses =
        base.accessedAddresses ∧
      ∀ a : Adr, (temporalSloadBase sevm base key).getCode a =
        base.getCode a := by
  unfold temporalSloadBase
  split <;> exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

private theorem temporalSloadBase_error (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).error = base.error :=
  (temporalSloadBase_carriers sevm base key).1

private theorem temporalSloadBase_output (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).output = base.output :=
  (temporalSloadBase_carriers sevm base key).2.1

private theorem temporalSloadBase_accessedAddresses (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).accessedAddresses =
      base.accessedAddresses :=
  (temporalSloadBase_carriers sevm base key).2.2.1

/-! ## Slot-pair inequalities lifted to accessed-key pairs -/

private theorem addAccessedStorageKey_getStorVal (devm : Devm) (a : Adr)
    (k : B256) (a' : Adr) (key : B256) :
    (addAccessedStorageKey devm a k).getStorVal a' key =
      devm.getStorVal a' key := rfl

private theorem addAccessedStorageKey_accessedStorageKeys' (devm : Devm)
    (a : Adr) (k : B256) :
    (addAccessedStorageKey devm a k).accessedStorageKeys =
      devm.accessedStorageKeys.insert (a, k) := rfl

private theorem addAccessedStorageKey_accessedAddresses (devm : Devm) (a : Adr)
    (k : B256) : (addAccessedStorageKey devm a k).accessedAddresses =
      devm.accessedAddresses := rfl

private theorem addAccessedStorageKey_error (devm : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey devm a k).error = devm.error := rfl

private theorem addAccessedStorageKey_output (devm : Devm) (a : Adr)
    (k : B256) : (addAccessedStorageKey devm a k).output = devm.output := rfl

private theorem addAccessedStorageKey_logs (devm : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey devm a k).logs = devm.logs := rfl

private theorem lengthWritePost_error (sevm : Sevm) (base : Devm) (ol : B256) :
    (lengthWritePost sevm base ol).error = base.error := rfl

private theorem lengthWritePost_output (sevm : Sevm) (base : Devm) (ol : B256) :
    (lengthWritePost sevm base ol).output = base.output := rfl

private theorem lengthWritePost_logs (sevm : Sevm) (base : Devm) (ol : B256) :
    (lengthWritePost sevm base ol).logs = base.logs := rfl

private theorem lengthWritePost_accessedAddresses (sevm : Sevm) (base : Devm)
    (ol : B256) : (lengthWritePost sevm base ol).accessedAddresses =
      base.accessedAddresses := rfl

private theorem keyPairNe {a₁ a₂ : Adr} {k₁ k₂ : B256} (h : k₂ ≠ k₁) :
    (a₁, k₁) ≠ (a₂, k₂) := fun hp => h (congrArg Prod.snd hp).symm

/-! ## The accessed-key set, stage by stage

The row-19 walk enters with both accessed sets empty, so each
`temporalSloadBase` layer resolves to its cold arm and the accessed-key set
grows by exactly the read key.  These shapes are what the cold cost equations
below read off; every non-membership is settled by slot separation, never by
deciding a `HashSet`. -/


private theorem temporalSloadBase_keys (sevm : Sevm) (base : Devm)
    (key : B256) :
    (temporalSloadBase sevm base key).accessedStorageKeys =
      if (sevm.currentTarget, key) ∈ base.accessedStorageKeys
        then base.accessedStorageKeys
        else base.accessedStorageKeys.insert (sevm.currentTarget, key) := by
  unfold temporalSloadBase
  split <;> rfl

private theorem temporalSloadBase_cold_keys (sevm : Sevm) (base : Devm)
    (key : B256)
    (h : (sevm.currentTarget, key) ∉ base.accessedStorageKeys) :
    (temporalSloadBase sevm base key).accessedStorageKeys =
      base.accessedStorageKeys.insert (sevm.currentTarget, key) := by
  rw [temporalSloadBase_keys, if_neg h]

private theorem stubRunKeys_expiryBase :
    (pauseExpiryBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256).accessedStorageKeys =
    Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256) := by
  unfold pauseExpiryBase temporalSloadBase
  rw [if_neg (show (stubPauseWorldSevm.currentTarget,
      assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost stubPauseWorldSevm stubPauseWorldPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem stubRunKeys_durationBase :
    (pauseDurationBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    (Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser) := by
  have hnot : (stubPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase stubPauseWorldSevm stubPauseWorldPre
        pauseWorldCallee.toB256).accessedStorageKeys := by
    rw [stubRunKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry
  unfold pauseDurationBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseExpiryBase stubPauseWorldSevm stubPauseWorldPre
    pauseWorldCallee.toB256).accessedStorageKeys).insert
    (stubPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) = _
  rw [stubRunKeys_expiryBase]
  rfl

private theorem stubRunKeys_kernelBase :
    (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    ((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot) := by
  have hnot : (stubPauseWorldSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase stubPauseWorldSevm stubPauseWorldPre
        pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
    rw [stubRunKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm
  unfold pauseKernelBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseDurationBase stubPauseWorldSevm stubPauseWorldPre
    pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys).insert
    (stubPauseWorldSevm.currentTarget, pauseDurationSlot) = _
  rw [stubRunKeys_durationBase]
  rfl

private theorem stubRunWarm_assign_kernelBase :
    (stubPauseWorldSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∈
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
  rw [stubRunKeys_kernelBase]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

private theorem stubRunKeys_assignPost :
    (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys = (((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)) := by
  show (assignmentBase stubPauseWorldSevm (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser)
    pauseWorldCallee.toB256).accessedStorageKeys = _
  unfold assignmentBase temporalSloadBase
  rw [if_pos stubRunWarm_assign_kernelBase]
  exact stubRunKeys_kernelBase

private theorem stubRunKeys_countBase :
    (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys = ((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)) := by
  have hnot : (stubPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys := by
    rw [stubRunKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count
  unfold temporalSloadBase
  rw [if_neg hnot]
  show ((assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys).insert
    (stubPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) = _
  rw [stubRunKeys_assignPost]
  rfl

private theorem stubRunKeys_removeBase1 :
    (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys = (((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)) := by
  have hnot : (stubPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys := by
    show _ ∉ (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [stubRunKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee
  rw [temporalSloadBase_cold_keys _ _ _ hnot]
  show ((temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys).insert
    (stubPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) = _
  rw [stubRunKeys_countBase]
  rfl

private theorem stubRunKeys_removeBase2 :
    (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys = ((((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, arrayLengthSlot)) := by
  have hnot : (stubPauseWorldSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys := by
    rw [stubRunKeys_removeBase1]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_length_ne_indexCallee.symm
    · exact pauseWorld_length_ne_count.symm
    · exact pauseWorld_duration_ne_length
    · exact pauseWorld_length_ne_expiry.symm
    · exact pauseWorld_length_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, stubRunKeys_removeBase1]
  rfl

private theorem stubRunKeys_removeBase3 :
    (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys = (((((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, arrayLengthSlot)).insert
      (configWorldOwner, arrayEntrySlot 1)) := by
  have hnot : (stubPauseWorldSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys := by
    rw [stubRunKeys_removeBase2]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · exact pauseWorld_length_ne_entryOne
    · exact pauseWorld_entryOne_ne_indexCallee.symm
    · exact pauseWorld_entryOne_ne_count.symm
    · exact pauseWorld_duration_ne_entryOne
    · exact pauseWorld_entryOne_ne_expiry.symm
    · exact pauseWorld_entryOne_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, stubRunKeys_removeBase2]
  rfl

/-! ## One-layer projection helpers -/

/-! ## One-layer projection helpers -/

private theorem temporalSstorePost_error (sevm : Sevm) (base : Devm)
    (key value : B256) :
    (temporalSstorePost sevm base key value).error = base.error := rfl

private theorem temporalSstorePost_output (sevm : Sevm) (base : Devm)
    (key value : B256) :
    (temporalSstorePost sevm base key value).output = base.output := rfl

private theorem temporalSstorePost_transientStorage (sevm : Sevm)
    (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).transientStorage =
      base.transientStorage := rfl

private theorem temporalSstorePost_accessedAddresses (sevm : Sevm)
    (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).accessedAddresses =
      base.accessedAddresses := rfl

private theorem addLog_getCode (devm : Devm) (l : Log) (x : Adr) :
    (devm.addLog l).getCode x = devm.getCode x := rfl

private theorem addLog_logs (devm : Devm) (l : Log) :
    (devm.addLog l).logs = devm.logs ++ [l] := rfl

private theorem addLog_error (devm : Devm) (l : Log) :
    (devm.addLog l).error = devm.error := rfl

private theorem addLog_output (devm : Devm) (l : Log) :
    (devm.addLog l).output = devm.output := rfl

private theorem addLog_transientStorage (devm : Devm) (l : Log) :
    (devm.addLog l).transientStorage = devm.transientStorage := rfl

private theorem addLog_accessedStorageKeys (devm : Devm) (l : Log) :
    (devm.addLog l).accessedStorageKeys = devm.accessedStorageKeys := rfl

private theorem addLog_accessedAddresses (devm : Devm) (l : Log) :
    (devm.addLog l).accessedAddresses = devm.accessedAddresses := rfl

private theorem addLog_getStorVal (devm : Devm) (l : Log) (a : Adr)
    (key : B256) : (devm.addLog l).getStorVal a key = devm.getStorVal a key :=
  rfl

private theorem setTransVal_getStorVal (devm : Devm) (a : Adr) (k v : B256)
    (a' : Adr) (key : B256) :
    (devm.setTransVal a k v).getStorVal a' key = devm.getStorVal a' key := rfl

private theorem setTransVal_logs (devm : Devm) (a : Adr) (k v : B256) :
    (devm.setTransVal a k v).logs = devm.logs := rfl

private theorem setTransVal_error (devm : Devm) (a : Adr) (k v : B256) :
    (devm.setTransVal a k v).error = devm.error := rfl

private theorem setTransVal_output (devm : Devm) (a : Adr) (k v : B256) :
    (devm.setTransVal a k v).output = devm.output := rfl

private theorem setMach_getStorVal (devm : Devm) (m : Mach) (a : Adr)
    (key : B256) : (devm.setMach m).getStorVal a key = devm.getStorVal a key :=
  rfl

private theorem setMach_getTransVal (devm : Devm) (m : Mach) (a : Adr)
    (key : B256) :
    (devm.setMach m).getTransVal a key = devm.getTransVal a key := rfl

private theorem setMach_logs (devm : Devm) (m : Mach) :
    (devm.setMach m).logs = devm.logs := rfl

private theorem setMach_error (devm : Devm) (m : Mach) :
    (devm.setMach m).error = devm.error := rfl

private theorem setMach_output (devm : Devm) (m : Mach) :
    (devm.setMach m).output = devm.output := rfl

/-! ## The cold and warm charges, resolved at the row-19 world -/

private theorem stubRunCost_assignment :
    temporalSloadCost stubPauseWorldSevm (pauseLockPost stubPauseWorldSevm stubPauseWorldPre)
      (assignmentSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (stubPauseWorldSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost stubPauseWorldSevm stubPauseWorldPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem stubRunCost_expiry :
    temporalSloadCost stubPauseWorldSevm
      (pauseExpiryBase stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256)
      (expirySlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (stubPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256).accessedStorageKeys from by
    rw [stubRunKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry)]
  rfl

private theorem stubRunCost_duration :
    temporalSloadCost stubPauseWorldSevm
      (pauseDurationBase stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser)
      pauseDurationSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (stubPauseWorldSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256
        pauseWorldPauser).accessedStorageKeys from by
    rw [stubRunKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm)]
  rfl

private theorem stubRunCost_assignWarm :
    temporalSloadCost stubPauseWorldSevm (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser)
      (assignmentSlot pauseWorldCallee.toB256) = 100 := by
  unfold temporalSloadCost
  rw [if_pos stubRunWarm_assign_kernelBase]
  rfl

private theorem stubRunCost_countCold :
    temporalSloadCost stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (stubPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys from by
    rw [stubRunKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count)]
  rfl

private theorem stubRunCost_idxCold :
    temporalSloadCost stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (stubPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys from by
    show _ ∉ (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [stubRunKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee)]
  rfl

private theorem stubRunCost_lenCold :
    temporalSloadCost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (stubPauseWorldSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys from by
    rw [stubRunKeys_removeBase1]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_length_ne_indexCallee.symm
    · exact pauseWorld_length_ne_count.symm
    · exact pauseWorld_duration_ne_length
    · exact pauseWorld_length_ne_expiry.symm
    · exact pauseWorld_length_ne_assignCallee.symm)]
  rfl

private theorem stubRunCost_arrCold :
    temporalSloadCost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (stubPauseWorldSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys from by
    rw [stubRunKeys_removeBase2]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · exact pauseWorld_length_ne_entryOne
    · exact pauseWorld_entryOne_ne_indexCallee.symm
    · exact pauseWorld_entryOne_ne_count.symm
    · exact pauseWorld_duration_ne_entryOne
    · exact pauseWorld_entryOne_ne_expiry.symm
    · exact pauseWorld_entryOne_ne_assignCallee.symm)]
  rfl

private theorem stubRunWarm_count_rb3 :
    (stubPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [stubRunKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))

private theorem stubRunWarm_expiry_rb3 :
    (stubPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [stubRunKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (Std.HashSet.mem_insert.mpr
        (Or.inr Std.HashSet.mem_insert_self)))))))))

/-! ## Storage read through the tower, stage by stage

Each lemma peels exactly one named layer by rewrite, per the substrate's
one-layer transport discipline. -/

private theorem stubRunStor_lockPost (key : B256) :
    (pauseLockPost stubPauseWorldSevm stubPauseWorldPre).getStorVal configWorldOwner key =
      pauseLastWorldStor.get key := by
  show stubPauseWorldPre.getStorVal configWorldOwner key = _
  exact stubPauseWorld_getStorVal

private theorem stubRunStor_kernelBase (key : B256) :
    (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact stubRunStor_lockPost key

private theorem stubRunStor_assignPost_other {key : B256}
    (h : assignmentSlot pauseWorldCallee.toB256 ≠ key) :
    (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  unfold assignmentPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe h)]
  unfold assignmentBase
  rw [temporalSloadBase_getStorVal]
  exact stubRunStor_kernelBase key

private theorem stubRunStor_assignPost_self :
    (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  unfold assignmentPost
  exact temporalSstorePost_self _ _ _ _

private theorem stubRunStor_countPost_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hc),
    temporalSloadBase_getStorVal]
  exact stubRunStor_assignPost_other ha

private theorem stubRunStor_countPost_assign :
    (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
    (keyPairNe pauseWorld_assignCallee_ne_count.symm),
    temporalSloadBase_getStorVal]
  exact stubRunStor_assignPost_self

private theorem stubRunStor_countPost_count :
    (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 :=
  temporalSstorePost_self _ _ _ _

private theorem stubRunStor_removeBase3_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact stubRunStor_countPost_other ha hc

private theorem stubRunStor_removeBase3_count :
    (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact stubRunStor_countPost_count

private theorem stubRunStor_removeBase3_assign :
    (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact stubRunStor_countPost_assign

/-! The five removal-walk writes, peeled from the outside of `B6`:
`indexClearPost` writes the index clear over the length restore, and
`entryClearPost` writes the tail clear over the moved-index and hole
writes. -/

private theorem stubRunStor_B6_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key)
    (hr : arrayEntrySlot 1 ≠ key)
    (hi : indexSlot pauseWorldCallee.toB256 ≠ key)
    (hl : arrayLengthSlot ≠ key) :
    (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hl),
    show (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost stubPauseWorldSevm
      (indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr),
    show indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr)]
  exact stubRunStor_removeBase3_other ha hc

private theorem stubRunStor_B6_index :
    (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (indexSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem stubRunStor_B6_length :
    (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner arrayLengthSlot = 0 := by
  rw [show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_indexCallee.symm),
    show lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem stubRunStor_B6_entry :
    (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (arrayEntrySlot 1) = 0 := by
  rw [show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_indexCallee.symm),
    show lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_entryOne),
    show (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost stubPauseWorldSevm
      (indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem stubRunStor_B6_assign :
    (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_assignCallee),
    show (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost stubPauseWorldSevm
      (indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_assignCallee),
    show indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_assignCallee)]
  exact stubRunStor_removeBase3_assign

private theorem stubRunStor_B6_count :
    (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_count),
    show (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost stubPauseWorldSevm
      (indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count),
    show indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count)]
  exact stubRunStor_removeBase3_count

/-! ## The staged memory and its image, through the walk's writes

`pauseMemory`'s five scratch words are staged by the body; the kernel saves
the old pauser at `previousPauserWord`, and the removal walk writes its three
scratch words above it.  Every write stays inside the `768`-byte image, so no
extension is ever charged. -/

private theorem stubRunMem_wf1 : Mem.Wf ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨hwf, -⟩
  exact hwf.write _ _

/-- The stage-one facts of the kernel-saved memory, read off
`pauseMemory_spec` in one destructuring: the written image, the unmoved `768`
size, and the two staged words the kernel's write must not disturb.  The four
named facts below are its projections. -/
private theorem stubRunMem_stage1 :
    Mem.Reads ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) ∧
    ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 ∧
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD
        (targetWord * 32).toNat 32 0) = pauseWorldCallee.toB256 ∧
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD
        (newPauserWord * 32).toNat 32 0) = 0 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with
    ⟨hwf, hreads, hsize, -, -, htarget, hnew, -⟩
  refine ⟨Mem.Reads.write hwf hreads _ _, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hsize]
      decide)]
    exact hsize
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew

private theorem stubRunMem_reads1 : Mem.Reads ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) :=
  stubRunMem_stage1.1

private theorem stubRunMem_size1 : ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 :=
  stubRunMem_stage1.2.1

private theorem stubRunMem_target1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 :=
  stubRunMem_stage1.2.2.1

private theorem stubRunMem_new1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
  stubRunMem_stage1.2.2.2

private theorem stubRunMem_wfLast : Mem.Wf (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  ((stubRunMem_wf1.write _ _).write _ _).write _ _

private theorem stubRunMem_readsLast : Mem.Reads (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  Mem.Reads.write ((stubRunMem_wf1.write _ _).write _ _)
    (Mem.Reads.write (stubRunMem_wf1.write _ _)
      (Mem.Reads.write stubRunMem_wf1 stubRunMem_reads1 _ _) _ _) _ _

private theorem stubRunMem_sizeIdx : (((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, stubRunMem_size1]
    decide)]
  exact stubRunMem_size1

private theorem stubRunMem_sizeLen : ((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, stubRunMem_sizeIdx]
    decide)]
  exact stubRunMem_sizeIdx

private theorem stubRunMem_sizeLast : (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, stubRunMem_sizeLen]
    decide)]
  exact stubRunMem_sizeLen

private theorem stubRunMem_targetLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact stubRunMem_target1

private theorem stubRunMem_newLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact stubRunMem_new1

/-- The three scratch words of the four-write image no later write disturbs,
in one bundle: the saved pauser survives at its own offset below every later
write, and the continuation and duration words sit above them all.  The three
named facts below are its projections. -/
private theorem stubRunMem_lastWords :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser ∧
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 ∧
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (durationWord * 32).toNat 32 0) =
      pauseWorldDuration := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with
    ⟨-, -, -, -, -, -, -, -, hcont, hdur⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      show 32 = pauseWorldPauser.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide)]
    exact hcont
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide)]
    exact hdur

private theorem stubRunMem_prevLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser :=
  stubRunMem_lastWords.1

private theorem stubRunMem_contLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 :=
  stubRunMem_lastWords.2.1

private theorem stubRunMem_durLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (durationWord * 32).toNat 32 0) =
      pauseWorldDuration :=
  stubRunMem_lastWords.2.2

/-! ## Value charges -/

private theorem stubRunSvc_reset {orig new : B256} (hnew : orig ≠ new)
    (hzero : ¬ orig = 0) : sstoreValueCost orig orig new = 2900 := by
  rw [sstoreValueCost, if_pos ⟨rfl, hnew⟩, if_neg hzero]
  norm_num [gasStorageUpdate, gasColdSload]

private theorem stubRunSvc_noop {orig cur : B256} :
    sstoreValueCost orig cur cur = 100 := by
  rw [sstoreValueCost, if_neg (by simp)]
  rfl

/-! ## The kernel prefix reserve, closed -/

private theorem stubRunKernelPrefixGas :
    foundSetPauserKernelPrefixGas stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
        pauseWorldCallee.toB256 pauseWorldPauser)
      pauseWorldCallee.toB256 0 pauseWorldPauser 2900 2900 = 8122 := by
  unfold foundSetPauserKernelPrefixGas
  rw [stubRunCost_assignWarm, stubRunCost_countCold]

/-! ## `B6` peels for the frame-meta fields -/

/-! ## Staged-memory sizes past the crossings -/

private theorem stubRunMem_sizeStaged1 : ((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, stubRunMem_sizeLast]
    decide)]
  exact stubRunMem_sizeLast

private theorem stubRunMem_sizeStaged2 : (((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseWorldDuration.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, stubRunMem_sizeStaged1]
    decide)]
  exact stubRunMem_sizeStaged1

private theorem stubRunMem_sizeStaged3 : ((((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseWorldDuration.toBytes).write 256 isPausedSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, stubRunMem_sizeStaged2]
    decide)]
  exact stubRunMem_sizeStaged2

private theorem stubRunMem_size8 :
    (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseWorldDuration).size = 768 := by
  unfold pauseDecodedMemory pauseStagedMemory
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, stubRunMem_sizeStaged3]
    decide)]
  exact stubRunMem_sizeStaged3

/-! ## Every other canonical pauser's expiry cell, separated from the walk's
writes -/

/-! ## Account-set and code reads at the `pauseAfterSet` boundary -/

/-- Neither the refund-counter update nor the storage-cell write inside
`temporalSstorePost` touches any account's code, shown directly at the
`State` level. -/
private theorem temporalSstorePost_getCode (sevm : Sevm) (base : Devm)
    (k v : B256) (a : Adr) :
    (temporalSstorePost sevm base k v).getCode a = base.getCode a := by
  show (((base.withRefundCounter _).state.setStorVal
    sevm.currentTarget k v).get a).code = ((base.state.get a)).code
  unfold State.setStorVal
  by_cases h : sevm.currentTarget = a
  · subst h
    rw [State.get_set_self]
    rfl
  · rw [State.get_set_ne _ h]
    rfl

private theorem temporalSloadBase_getCode (sevm : Sevm) (base : Devm)
    (key : B256) (a : Adr) :
    (temporalSloadBase sevm base key).getCode a = base.getCode a :=
  (temporalSloadBase_carriers sevm base key).2.2.2 a


private theorem addAccessedStorageKey_getCode (devm : Devm) (a : Adr)
    (k : B256) (x : Adr) :
    (addAccessedStorageKey devm a k).getCode x = devm.getCode x := rfl

private theorem lengthWritePost_getCode (sevm : Sevm) (base : Devm) (ol : B256)
    (x : Adr) : (lengthWritePost sevm base ol).getCode x = base.getCode x :=
  temporalSstorePost_getCode sevm base arrayLengthSlot ol x

private theorem stubRunAddrs_B7 :
    ((indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨stubPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  rw [addLog_accessedAddresses,
    show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost stubPauseWorldSevm
      (indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_accessedAddresses,
    show entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSstorePost_accessedAddresses,
    temporalSloadBase_accessedAddresses]
  show (assignmentPost stubPauseWorldSevm
    (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedAddresses = _
  unfold assignmentPost
  rw [temporalSstorePost_accessedAddresses]
  unfold assignmentBase
  rw [temporalSloadBase_accessedAddresses]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses]
  rfl

private theorem stubRunCode_B7 :
    ((indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨stubPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = PinnedTargetControl.stubCode := by
  rw [show ((indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨stubPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr from rfl,
    show (indexClearPost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost stubPauseWorldSevm
      (lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_getCode,
    show lengthWritePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost stubPauseWorldSevm (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_getCode,
    show (entryClearPost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost stubPauseWorldSevm
      (indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_getCode,
    show indexWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_getCode,
    show entryWritePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost stubPauseWorldSevm
      (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (temporalSstorePost stubPauseWorldSevm (temporalSloadBase stubPauseWorldSevm (assignmentPost stubPauseWorldSevm
      (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_getCode,
    temporalSloadBase_getCode, temporalSloadBase_getCode,
    temporalSloadBase_getCode, temporalSstorePost_getCode,
    temporalSloadBase_getCode]
  show (assignmentPost stubPauseWorldSevm
    (pauseKernelBase stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr =
    PinnedTargetControl.stubCode
  unfold assignmentPost
  rw [temporalSstorePost_getCode]
  unfold assignmentBase
  rw [temporalSloadBase_getCode]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getCode, temporalSloadBase_getCode,
    temporalSloadBase_getCode]
  show stubPauseWorldPre.state.getCode pauseWorldCallee.toB256.toAdr = PinnedTargetControl.stubCode
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  exact stubPauseWorld_targetCodeAt

private theorem stubRunMem_wf8 :
    Mem.Wf (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseWorldDuration) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact (((stubRunMem_wfLast.write _ _).write _ _).write _ _).write _ _

private theorem stubRunMem_reads8 :
    Mem.Reads (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseWorldDuration) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact Mem.Reads.write (((stubRunMem_wfLast.write _ _).write _ _).write _ _)
    (Mem.Reads.write ((stubRunMem_wfLast.write _ _).write _ _)
      (Mem.Reads.write (stubRunMem_wfLast.write _ _)
        (Mem.Reads.write stubRunMem_wfLast stubRunMem_readsLast _ _) _ _) _ _) _ _

private theorem stubRunMem_target8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
  exact stubRunMem_targetLast

private theorem stubRunMem_dur8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes).sliceD (durationWord * 32).toNat 32 0) =
      pauseWorldDuration := by
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
  exact stubRunMem_durLast

private theorem state_setBal_stor_local (st : State) (adr : Adr)
    (val : B256) (a : Adr) :
    ((st.setBal adr val).get a).stor = (st.get a).stor := by
  by_cases h : adr = a
  · subst h
    unfold State.setBal
    rw [State.get_set_self]
    rfl
  · exact congrArg Acct.stor (State.get_set_ne st h _)

private theorem state_addBal_stor_local (st : State) (adr : Adr)
    (val : B256) (a : Adr) :
    ((st.addBal adr val).get a).stor = (st.get a).stor := by
  unfold State.addBal
  exact state_setBal_stor_local st adr _ a

private theorem state_subBal_stor_local {st st' : State} {adr : Adr}
    {val : B256} (h : st.subBal adr val = some st') (a : Adr) :
    (st'.get a).stor = (st.get a).stor := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with hstate
    subst hstate
    exact state_setBal_stor_local st adr _ a

private theorem state_setStorVal_stor_ne_local (st : State)
    {writer reader : Adr} (h : writer ≠ reader) (key value : B256) :
    ((st.setStorVal writer key value).get reader).stor =
      (st.get reader).stor := by
  unfold State.setStorVal
  exact congrArg Acct.stor (State.get_set_ne st h _)

private def stubRunKernelBase : Devm :=
  pauseKernelBase stubPauseWorldSevm stubPauseWorldPre
    pauseWorldCallee.toB256 pauseWorldPauser

private def stubRunCountPost : Devm :=
  temporalSstorePost stubPauseWorldSevm
    (temporalSloadBase stubPauseWorldSevm
      (assignmentPost stubPauseWorldSevm stubRunKernelBase
        pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
    (countSlot pauseWorldPauser) 0

private def stubRunRemoveBase3 : Devm :=
  temporalSloadBase stubPauseWorldSevm
    (temporalSloadBase stubPauseWorldSevm
      (temporalSloadBase stubPauseWorldSevm stubRunCountPost
        (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
    (arrayEntrySlot 1)

private def stubRunAfterSetBase : Devm :=
  (indexClearPost stubPauseWorldSevm
    (entryClearPost stubPauseWorldSevm stubRunRemoveBase3
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0).addLog
      ⟨stubPauseWorldSevm.currentTarget,
        [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩

private def stubRunMemoryLast : Mem :=
  ((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
    (removedIndexWord * 32).toNat (1 : B256).toBytes).write
    (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
    (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes

private def stubRunImageLast : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
          (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
        (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
    (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes

/-! ## The composed run -/

/-- The row-19 master composition: the boundary walk with its dichotomy
interface facts, and the complete message run with its settled effects. -/

private theorem stubPauseWorld_targetPausedZero :
    stubPauseWorldPre.getStorVal pauseWorldCallee
      PinnedTargetControl.pausedUntilSlot = 0 := by
  change (stubPauseWorldState.get pauseWorldCallee).stor.get
      PinnedTargetControl.pausedUntilSlot = 0
  rw [stubPauseWorldState_get_target]
  rfl

private theorem stubPauseWorld_targetPausedOrigZero :
    getOrigStorVal stubPauseWorldSevm pauseWorldCallee
      PinnedTargetControl.pausedUntilSlot = 0 := by
  change (stubPauseWorldState.get pauseWorldCallee).stor.get
      PinnedTargetControl.pausedUntilSlot = 0
  rw [stubPauseWorldState_get_target]
  rfl

private theorem stubPauseWorld_targetPausedCold :
    (pauseWorldCallee, PinnedTargetControl.pausedUntilSlot) ∉
      stubPauseWorldPre.accessedStorageKeys := by
  rw [show stubPauseWorldPre.accessedStorageKeys =
      Std.HashSet.emptyWithCapacity from rfl]
  exact Std.HashSet.not_mem_emptyWithCapacity

private theorem stubRunAfterSetBase_code :
    stubRunAfterSetBase.getCode pauseWorldCallee.toB256.toAdr =
      PinnedTargetControl.stubCode := by
  simpa only [stubRunAfterSetBase, stubRunRemoveBase3, stubRunCountPost,
    stubRunKernelBase] using stubRunCode_B7

private theorem stubRunAfterSetBase_targetPausedCold :
    (pauseWorldCallee.toB256.toAdr,
      PinnedTargetControl.pausedUntilSlot) ∉
      stubRunAfterSetBase.accessedStorageKeys := by
  rw [stubRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  unfold stubRunRemoveBase3 stubRunCountPost stubRunKernelBase
  rw [stubRunKeys_removeBase3]
  simp only [Std.HashSet.mem_insert,
    Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or,
    beq_iff_eq, Prod.mk.injEq, not_and]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals
    intro _
    apply pauseWorld_callee_ne_owner
    rw [← show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
    exact h.symm

private theorem temporalSstorePost_getStorVal_otherAddress
    (sevm : Sevm) (base : Devm) (writeKey value : B256)
    (a : Adr) (key : B256) (hne : a ≠ sevm.currentTarget) :
    (temporalSstorePost sevm base writeKey value).getStorVal a key =
      base.getStorVal a key := by
  exact temporalSstorePost_other sevm base writeKey value a key
    (fun h => hne (congrArg Prod.fst h))

private theorem stubRunAfterSetBase_targetPausedZero :
    stubRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      PinnedTargetControl.pausedUntilSlot = 0 := by
  have haddr : pauseWorldCallee.toB256.toAdr ≠
      stubPauseWorldSevm.currentTarget := stubPauseWorld_target_ne_owner
  unfold stubRunAfterSetBase
  rw [addLog_getStorVal]
  unfold indexClearPost lengthWritePost entryClearPost indexWritePost
    entryWritePost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr]
  unfold stubRunRemoveBase3
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  unfold stubRunCountPost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSloadBase_getStorVal]
  unfold assignmentPost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr]
  unfold assignmentBase stubRunKernelBase pauseKernelBase pauseDurationBase
    pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  exact stubPauseWorld_targetPausedZero

private theorem stubRunAfterSetBase_count :
    stubRunAfterSetBase.getStorVal configWorldOwner
      (countSlot pauseWorldPauser) = 0 := by
  rw [stubRunAfterSetBase, addLog_getStorVal]
  simpa only [stubRunRemoveBase3, stubRunCountPost, stubRunKernelBase] using
    stubRunStor_B6_count

private theorem stubRunAfterSetBase_interval :
    stubRunAfterSetBase.getStorVal configWorldOwner heartbeatIntervalSlot =
      pauseWorldInterval := by
  rw [stubRunAfterSetBase, addLog_getStorVal]
  have h := (stubRunStor_B6_other
    pauseWorld_interval_ne_assignCallee.symm
    pauseWorld_interval_ne_count.symm
    pauseWorld_interval_ne_entryOne.symm
    pauseWorld_interval_ne_indexCallee.symm
    pauseWorld_interval_ne_length.symm).trans pauseLastStor_interval
  simpa only [stubRunRemoveBase3, stubRunCountPost, stubRunKernelBase] using h

private theorem stubRunAfterSetBase_expiry :
    stubRunAfterSetBase.getStorVal configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  rw [stubRunAfterSetBase, addLog_getStorVal]
  have h := (stubRunStor_B6_other pauseWorld_assignCallee_ne_expiry
    pauseWorld_count_ne_expiry pauseWorld_entryOne_ne_expiry
    pauseWorld_indexCallee_ne_expiry pauseWorld_length_ne_expiry).trans
      pauseLastStor_expiry
  simpa only [stubRunRemoveBase3, stubRunCountPost, stubRunKernelBase] using h

private theorem stubRunAfterSetBase_accessedAddresses :
    stubRunAfterSetBase.accessedAddresses = Std.HashSet.emptyWithCapacity := by
  simpa only [stubRunAfterSetBase, stubRunRemoveBase3, stubRunCountPost,
    stubRunKernelBase] using stubRunAddrs_B7

private theorem memWordAt_of_reads_toB256 {devm : Devm} {img : Bytes}
    {offset : Nat} {word : B256} (hwf : Mem.Wf devm.memory)
    (hreads : Mem.Reads devm.memory img)
    (hword : Bytes.toB256 (img.sliceD offset 32 0) = word) :
    MemWordAt devm offset word := by
  refine ⟨hwf, img, hreads, ?_⟩
  have hlen : (img.sliceD offset 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rw [← hword, Bytes.toBytes_toB256_of_length hlen]

private theorem stubRunAfterSetBase_warmCount :
    (stubPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
      stubRunAfterSetBase.accessedStorageKeys := by
  rw [stubRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [stubRunRemoveBase3, stubRunCountPost, stubRunKernelBase] using
    stubRunWarm_count_rb3

private theorem stubRunAfterSetBase_warmExpiry :
    (stubPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
      stubRunAfterSetBase.accessedStorageKeys := by
  rw [stubRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [stubRunRemoveBase3, stubRunCountPost, stubRunKernelBase] using
    stubRunWarm_expiry_rb3

private theorem stubPauseWorld_afterSetStubSeam :
    ∃ mid : Devm,
      mid.stack = [] ∧
      mid.memory = pauseDecodedMemory stubRunMemoryLast pauseWorldDuration ∧
      mid.gasLeft = 42343 ∧
      (∀ key : B256,
        mid.getStorVal configWorldOwner key =
          stubRunAfterSetBase.getStorVal configWorldOwner key) ∧
      (stubPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      (stubPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      ∀ final : Devm,
        Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            stubPauseWorldSevm mid pauseSuccess final →
          Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            stubPauseWorldSevm
            (stubRunAfterSetBase.setMach
              ⟨[], stubRunMemoryLast, 67693⟩)
            pauseAfterSet final := by
  obtain ⟨mid, hstk, hmem, hgas, _herr, _hout, _hret, _hlogs,
      _hrefund, _hatd, _htrans, hask, _haddrs, _hpaused, hchain, hclose⟩ :=
    PinnedTargetStubWalk.pauseAfterSet_stub_toSuccess_runCompiled
      ((runtime officialParams).main :: (runtime officialParams).aux)
      stubPauseWorldSevm stubRunAfterSetBase pauseWorldCallee.toB256
      pauseWorldDuration stubRunMemoryLast stubRunImageLast 2600 42362
      (by simpa only [stubRunMemoryLast] using stubRunMem_wfLast)
      (by simpa only [stubRunMemoryLast, stubRunImageLast] using
        stubRunMem_readsLast)
      (by simpa only [stubRunImageLast] using stubRunMem_targetLast)
      (by simpa only [stubRunImageLast] using stubRunMem_durLast)
      (by simpa only [stubRunMemoryLast] using stubRunMem_sizeLast)
      (by
        unfold temporalAccountAccessCost
        rw [if_neg (show ¬ pauseWorldCallee.toB256.toAdr ∈
            stubRunAfterSetBase.accessedAddresses from by
          rw [stubRunAfterSetBase_accessedAddresses]
          exact Std.HashSet.not_mem_emptyWithCapacity)]
        rfl)
      stubRunAfterSetBase_code
      stubRunAfterSetBase_targetPausedZero
      (by simpa only [toAdr_toB256] using
        stubPauseWorld_targetPausedOrigZero)
      stubRunAfterSetBase_targetPausedCold
      rfl
      (by decide)
      (by decide)
      (by show (1024 : Nat) ≠ 0; decide)
      (by simpa only [toAdr_toB256] using
        stubPauseWorld_target_not_precompile)
      (by norm_num)
      (by norm_num)
  rcases hchain with ⟨st₁, st₂, hsub₁, hsub₂, hstate⟩
  have htargetOwner : pauseWorldCallee.toB256.toAdr ≠
      configWorldOwner := by
    simpa only [stubPauseWorld_currentTarget] using
      stubPauseWorld_target_ne_owner
  have hownerStor : (mid.state.get configWorldOwner).stor =
      (stubRunAfterSetBase.state.get configWorldOwner).stor := by
    rw [hstate]
    exact (state_addBal_stor_local st₂ pauseWorldCallee.toB256.toAdr 0
      configWorldOwner).trans
      ((state_subBal_stor_local hsub₂ configWorldOwner).trans
        ((state_setStorVal_stor_ne_local
          (st₁.addBal pauseWorldCallee.toB256.toAdr 0) htargetOwner
          PinnedTargetControl.pausedUntilSlot
          (pauseForProjection stubPauseWorldSevm.benvStat.time
            pauseWorldDuration)).trans
          ((state_addBal_stor_local st₁ pauseWorldCallee.toB256.toAdr 0
            configWorldOwner).trans
            (state_subBal_stor_local hsub₁ configWorldOwner))))
  have hstor : ∀ key : B256,
      mid.getStorVal configWorldOwner key =
        stubRunAfterSetBase.getStorVal configWorldOwner key := by
    intro key
    exact congrArg (fun stor => stor.get key) hownerStor
  refine ⟨mid, hstk, hmem, hgas, hstor,
    (hask _).mpr (Or.inr stubRunAfterSetBase_warmCount),
    (hask _).mpr (Or.inr stubRunAfterSetBase_warmExpiry), ?_⟩
  intro final hrun
  have h := hclose final hrun
  rw [show (42362 + 22731 + 2600 : Nat) = 67693 from by norm_num] at h
  exact h

private theorem stubPauseWorld_originalExpiry :
    getOrigStorVal stubPauseWorldSevm configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  change (stubPauseWorldState.get configWorldOwner).stor.get
    (expirySlot pauseWorldPauser) = pauseWorldExpiry
  rw [stubPauseWorldState_get_breaker]
  exact pauseLastStor_expiry

private def stubRunDecodedMemory : Mem :=
  pauseDecodedMemory stubRunMemoryLast pauseWorldDuration

private def stubRunImage8 : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt stubRunImageLast 256 pauseForSelector.toBytes)
        288 pauseWorldDuration.toBytes)
      256 isPausedSelector.toBytes)
    0 (1 : B256).toBytes

private def stubRunAfterSetNoLog : Devm :=
  indexClearPost stubPauseWorldSevm
    (entryClearPost stubPauseWorldSevm stubRunRemoveBase3
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0

private def stubRunMemory1 : Mem :=
  (pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

private def stubRunImage1 : Bytes :=
  Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

private theorem stubPauseWorld_getOrigStorVal (key : B256) :
    getOrigStorVal stubPauseWorldSevm configWorldOwner key =
      pauseLastWorldStor.get key := by
  change (stubPauseWorldState.get configWorldOwner).stor.get key = _
  rw [stubPauseWorldState_get_breaker]

private theorem stubPauseWorld_successSuffix :
    ∃ successPre final : Devm,
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm successPre pauseSuccess final ∧
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm
          (stubRunAfterSetBase.setMach
            ⟨[], stubRunMemoryLast, 67693⟩)
          pauseAfterSet final ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm
          (stubRunAfterSetBase.setMach
            ⟨[], stubRunMemoryLast, 67693⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference stubPauseWorldSevm
        (stubRunAfterSetBase.setMach
          ⟨[], stubRunMemoryLast, 67693⟩) successPre := by
  obtain ⟨mid, hstk, hmem, hgas, hstor, hwarmCount, hwarmExpiry, hclose⟩ :=
    stubPauseWorld_afterSetStubSeam
  have hmidCount : mid.getStorVal stubPauseWorldSevm.currentTarget
      (countSlot pauseWorldPauser) = 0 := by
    rw [stubPauseWorld_currentTarget, hstor]
    exact stubRunAfterSetBase_count
  have hmidExpiry : mid.getStorVal stubPauseWorldSevm.currentTarget
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
    rw [stubPauseWorld_currentTarget, hstor]
    exact stubRunAfterSetBase_expiry
  have hW8 := pauseSuccess_zeroCount_ok_runCompiled
    ((runtime officialParams).main :: (runtime officialParams).aux)
    stubPauseWorldSevm mid stubRunDecodedMemory stubRunImage8
    pauseWorldCallee.toB256 pauseWorldDuration pauseWorldPauser
    pauseWorldExpiry pauseWorldExpiry 100 2900 36021
    (by simpa only [stubRunDecodedMemory, stubRunMemoryLast] using
      stubRunMem_wf8)
    (by simpa only [stubRunDecodedMemory, stubRunMemoryLast, stubRunImage8,
      stubRunImageLast] using stubRunMem_reads8)
    (by simpa only [stubRunImage8, stubRunImageLast] using
      stubRunMem_target8)
    (by simpa only [stubRunImage8, stubRunImageLast] using stubRunMem_dur8)
    (by
      simpa only [stubRunDecodedMemory, stubRunMemoryLast] using
        stubRunMem_size8.ge)
    (by
      simpa only [stubRunDecodedMemory, stubRunMemoryLast] using
        (show (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256
          pauseWorldDuration).write (previousPauserWord * 32).toNat
          pauseWorldPauser.toBytes).write (removedIndexWord * 32).toNat
          (1 : B256).toBytes).write (arrayLengthWord * 32).toNat
          (1 : B256).toBytes).write (lastTargetWord * 32).toNat
          pauseWorldCallee.toB256.toBytes) pauseWorldDuration).size % 32 = 0
          from by rw [stubRunMem_size8]))
    stubPauseWorld_callerWord hmidCount
    (by
      unfold temporalSloadCost
      rw [if_pos hwarmCount]
      rfl)
    hmidExpiry
    (by
      rw [stubPauseWorld_currentTarget]
      exact stubPauseWorld_originalExpiry)
    hwarmExpiry
    (stubRunSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend])
    rfl
  have hmidEta : mid.setMach
      ⟨[], stubRunDecodedMemory, 36021 + 3322 + 100 + 2900⟩ = mid := by
    rw [show (36021 + 3322 + 100 + 2900 : Nat) = 42343 from by norm_num,
      stubRunDecodedMemory, ← hgas, ← hmem, ← hstk]
    rfl
  rw [hmidEta] at hW8
  have hafter := hclose _ hW8
  have hboundary := Func.RunCompiledTo.of_runCompiled hW8
  have hafterTo := Func.RunCompiledTo.of_runCompiled hafter
  refine ⟨mid, _, hW8, hafter, hboundary, hafterTo, ?_⟩
  unfold PauseSuccessNoninterference
  rw [stubPauseWorld_currentTarget, stubPauseWorld_callerWord]
  constructor
  · rw [hstor, setMach_getStorVal]
  · rw [hstor, setMach_getStorVal]

private theorem stubPauseWorld_productionRun :
    ∃ successPre final : Devm,
      Prog.RunCompiledTo stubPauseWorldSevm stubPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm
          (stubRunAfterSetBase.setMach
            ⟨[], stubRunMemoryLast, 67693⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference stubPauseWorldSevm
        (stubRunAfterSetBase.setMach
          ⟨[], stubRunMemoryLast, 67693⟩) successPre := by
  obtain ⟨successPre, final, hsuccess, hafter, hsuccessTo, hafterTo, hni⟩ :=
    stubPauseWorld_successSuffix
  have hfin := finishSetPauser_pauseAfterSet_runCompiled officialParams
    stubPauseWorldSevm stubRunAfterSetNoLog stubRunMemoryLast stubRunImageLast
    pauseWorldCallee.toB256 pauseWorldPauser 0 [] 67693 _ (by decide)
    (by simpa only [stubRunMemoryLast, stubRunImageLast] using
      stubRunMem_readsLast)
    (by simpa only [stubRunImageLast] using stubRunMem_targetLast)
    (by simpa only [stubRunImageLast] using stubRunMem_prevLast)
    (by simpa only [stubRunImageLast] using stubRunMem_newLast)
    (by simpa only [stubRunImageLast] using stubRunMem_contLast)
    (by rw [stubRunMemoryLast, stubRunMem_sizeLast]; decide)
    (by rw [stubRunMemoryLast, stubRunMem_sizeLast])
    rfl
    (by
      simpa only [stubRunAfterSetNoLog, stubRunAfterSetBase,
        stubRunRemoveBase3, stubRunCountPost, stubRunKernelBase] using hafter)
  rw [show (67693 + 1934 : Nat) = 69627 from by norm_num] at hfin
  have hrem := removeTarget_toFinish_coldEntry_runCompiled officialParams
    stubPauseWorldSevm stubRunCountPost stubRunMemory1 stubRunImage1
    pauseWorldCallee.toB256 0 1 [] (by decide)
    pauseWorldCallee.toB256 1 1
    2100 2100 2100 100 100 2900 2900 2900 69627 0
    (by simpa only [stubRunMemory1] using stubRunMem_wf1)
    (by simpa only [stubRunMemory1, stubRunImage1] using stubRunMem_reads1)
    (by simpa only [stubRunImage1] using stubRunMem_target1)
    pauseWorld_calleeValid
    (by decide) (by decide) 768 0 0 0
    (by simpa only [stubRunMemory1] using stubRunMem_size1)
    (by rw [stubRunMemory1, stubRunMem_size1])
    (by decide) (by decide) (by decide) (by decide)
    ((stubRunStor_countPost_other
      pauseWorld_entryOne_ne_assignCallee.symm
      pauseWorld_entryOne_ne_count.symm).trans pauseLastStor_entry)
    ((stubRunStor_countPost_other pauseWorld_assignCallee_ne_indexCallee
      pauseWorld_indexCallee_ne_count.symm).trans pauseLastStor_index)
    ((stubRunStor_countPost_other pauseWorld_length_ne_assignCallee.symm
      pauseWorld_length_ne_count.symm).trans pauseLastStor_length)
    ((stubPauseWorld_getOrigStorVal _).trans pauseLastStor_entry)
    ((stubPauseWorld_getOrigStorVal _).trans pauseLastStor_index)
    ((stubPauseWorld_getOrigStorVal _).trans pauseLastStor_length)
    stubRunCost_idxCold stubRunCost_lenCold stubRunCost_arrCold
    stubRunSvc_noop stubRunSvc_noop
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (by decide) (by norm_num [gCallStipend]) rfl _
    (by dsimp only; exact hfin)
  rw [show (0 + 69627 + 139 + 0 + 0 + 0 + 2100 + 2100 + 2100 + 100 +
    100 + 2900 + 2900 + 2900 : Nat) = 84966 from by norm_num] at hrem
  have hglue := afterOldPauser_removeTarget_runCompiled officialParams
    stubPauseWorldSevm stubRunCountPost stubRunMemory1 stubRunImage1 []
    84966 _ (by decide)
    (by simpa only [stubRunMemory1, stubRunImage1] using stubRunMem_reads1)
    (by simpa only [stubRunImage1] using stubRunMem_new1)
    (by rw [stubRunMemory1, stubRunMem_size1]; decide)
    (by rw [stubRunMemory1, stubRunMem_size1])
    hrem
  rw [show (84966 + 35 : Nat) = 85001 from by norm_num] at hglue
  have hker := setPauserKernel_found_runCompiled officialParams
    stubPauseWorldSevm stubRunKernelBase
    (pauseMemory pauseWorldCallee.toB256 pauseWorldDuration)
    (pauseImage pauseWorldCallee.toB256 pauseWorldDuration) _
    pauseWorldCallee.toB256 0 pauseWorldPauser 1 pauseWorldPauser 1
    2900 2900 85001 0
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseWorldDuration).2.2.2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseWorldDuration).2.2.2.2.2.2.1
    pauseWorld_calleeValid pauseWorld_pauserValid
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseWorldDuration).2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseWorldDuration).2.2.2.2.1
    ((stubRunStor_kernelBase _).trans pauseLastStor_assignment)
    ((stubPauseWorld_getOrigStorVal _).trans pauseLastStor_assignment)
    (stubRunSvc_reset (by decide) (by decide))
    ((stubRunStor_assignPost_other pauseWorld_assignCallee_ne_count).trans
      pauseLastStor_count)
    ((stubPauseWorld_getOrigStorVal _).trans pauseLastStor_count)
    (stubRunSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend]) rfl
    (by
      dsimp only [stubRunKernelBase, stubRunCountPost, stubRunMemory1,
        stubRunImage1]
      rw [show (1 - 1 : B256) = 0 from by decide]
      exact hglue)
  rw [show foundSetPauserKernelPrefixGas stubPauseWorldSevm
      stubRunKernelBase pauseWorldCallee.toB256 0 pauseWorldPauser
      2900 2900 = 8122 from by
        simpa only [stubRunKernelBase] using stubRunKernelPrefixGas,
    show (0 + 85001 + 8122 : Nat) = 93123 from by norm_num] at hker
  have hcalldata := pauseCalldata_facts
    stubPauseWorld_publicPausePremises.calldata
  have hbody := pause_body_runCompiled officialParams stubPauseWorldSevm
    stubPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser
    pauseWorldExpiry pauseWorldDuration 2100 2100 2100 93123 _
    hcalldata.1
    (by decide) rfl
    hcalldata.2
    stubPauseWorld_callerWord
    ((stubRunStor_lockPost _).trans pauseLastStor_assignment)
    stubRunCost_assignment
    (by
      unfold pauseExpiryBase
      rw [temporalSloadBase_getStorVal]
      exact (stubRunStor_lockPost _).trans pauseLastStor_expiry)
    stubRunCost_expiry
    (by decide)
    (by
      unfold pauseDurationBase pauseExpiryBase
      rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
      exact (stubRunStor_lockPost _).trans pauseLastStor_duration)
    stubRunCost_duration rfl hker
  rw [show (93123 + (469 + 2100 + 2100 + 2100) : Nat) = 99892 from by
    norm_num] at hbody
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  obtain ⟨hprog, _hcompile⟩ := pause_dispatch_runCompiledTo officialParams
    stubPauseWorldSevm stubPauseWorldPre 99892 0 _
    hcalldata.1
    stubPauseWorld_publicPausePremises.valueZero
    stubPauseWorld_publicPausePremises.selectorEq
    (by
      rw [stubPauseWorld_publicPausePremises.currentTarget]
      exact stubPauseWorld_publicPausePremises.codeAddress)
    stubPauseWorld_publicPausePremises.productionBytes hbodyTo
  have hentry : stubPauseWorldPre.setMach
      ⟨[], Mem.empty, 0 + pauseDispatchGas + 99892⟩ =
      stubPauseWorldPre := by
    rw [show (0 + pauseDispatchGas + 99892 : Nat) = stubPauseWorldGas from by
      norm_num [pauseDispatchGas, stubPauseWorldGas]]
    rfl
  rw [hentry] at hprog
  exact ⟨successPre, final, hprog, hsuccessTo, hafterTo, hni⟩

private def stubPauseWorldAfterSetEntry : Devm :=
  stubRunAfterSetBase.setMach ⟨[], stubRunMemoryLast, 67693⟩

private theorem stubPauseWorldAfterSetEntry_memory :
    stubPauseWorldAfterSetEntry.memory = stubRunMemoryLast := by
  rw [stubPauseWorldAfterSetEntry, Devm.memory_setMach]

private theorem stubRunMemoryLast_wf : Mem.Wf stubRunMemoryLast := by
  unfold stubRunMemoryLast
  exact stubRunMem_wfLast

private theorem stubRunMemoryLast_reads :
    Mem.Reads stubRunMemoryLast stubRunImageLast := by
  unfold stubRunMemoryLast stubRunImageLast
  exact stubRunMem_readsLast

private theorem stubRunImageLast_target :
    Bytes.toB256
      (stubRunImageLast.sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  unfold stubRunImageLast
  exact stubRunMem_targetLast

private theorem stubRunImageLast_duration :
    Bytes.toB256
      (stubRunImageLast.sliceD (durationWord * 32).toNat 32 0) =
      pauseWorldDuration := by
  unfold stubRunImageLast
  exact stubRunMem_durLast

private theorem stubRunMemoryLast_targetWindow {devm : Devm}
    (hmemory : devm.memory = stubRunMemoryLast) :
    MemWordAt devm (targetWord * 32).toNat pauseWorldCallee.toB256 := by
  unfold MemWordAt
  rw [hmemory]
  refine ⟨stubRunMemoryLast_wf, stubRunImageLast,
    stubRunMemoryLast_reads, ?_⟩
  have hlen :
      (stubRunImageLast.sliceD (targetWord * 32).toNat 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rw [← stubRunImageLast_target, Bytes.toBytes_toB256_of_length hlen]

private theorem stubRunMemoryLast_durationWindow {devm : Devm}
    (hmemory : devm.memory = stubRunMemoryLast) :
    MemWordAt devm (durationWord * 32).toNat pauseWorldDuration := by
  unfold MemWordAt
  rw [hmemory]
  refine ⟨stubRunMemoryLast_wf, stubRunImageLast,
    stubRunMemoryLast_reads, ?_⟩
  have hlen :
      (stubRunImageLast.sliceD (durationWord * 32).toNat 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rw [← stubRunImageLast_duration, Bytes.toBytes_toB256_of_length hlen]

private theorem stubPauseWorld_afterSetAt {final : Devm}
    (hafter : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      stubPauseWorldSevm stubPauseWorldAfterSetEntry pauseAfterSet
      (.ok final)) :
    PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256
      pauseWorldDuration PinnedTargetControl.stubCode (.ok final)
      stubPauseWorldAfterSetEntry := by
  refine ⟨?_, ?_, ?_, ?_, hafter⟩
  · exact stubRunMemoryLast_targetWindow
      stubPauseWorldAfterSetEntry_memory
  · exact stubRunMemoryLast_durationWindow
      stubPauseWorldAfterSetEntry_memory
  · unfold CodeAt stubPauseWorldAfterSetEntry
    change stubRunAfterSetBase.getCode pauseWorldCallee.toB256.toAdr = _
    exact stubRunAfterSetBase_code
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_callerWord]
    unfold stubPauseWorldAfterSetEntry
    rw [setMach_getStorVal, stubRunAfterSetBase_count,
      stubPauseWorld_getStorVal, pauseLastStor_count]
    decide

/-- A concrete production public pause with the installed pinned-target stub.
The theorem exposes the production run, exact `pauseAfterSet` entry, actual
`pauseSuccess` subrun, explicit callback noninterference, combined hook,
committed outcome family, and the final pinned-target conclusion. -/
theorem stubPauseWorld_closedPublicPause :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo stubPauseWorldSevm stubPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256
          pauseWorldDuration PinnedTargetControl.stubCode (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference stubPauseWorldSevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          stubPauseWorldSevm entry pauseWorldCallee
          PinnedTargetControl.stubProgram pauseWorldDuration (.ok final) ∧
      PublicPauseCommittedOutcomes stubPauseWorldSevm stubPauseWorldPre
          pauseWorldCallee.toB256 pauseWorldDuration
          PinnedTargetControl.stubCode (.ok final) ∧
      PublicPausePinnedTargetConclusion stubPauseWorldSevm
          stubPauseWorldPre pauseWorldCallee.toB256 pauseWorldDuration
          PinnedTargetControl.stubCode PinnedTargetControl.stubProgram
          PinnedTargetControl.pausedUntil (.ok final) final := by
  obtain ⟨successPre, final, hprog, hsuccess, hafter, hni⟩ :=
    stubPauseWorld_productionRun
  have hafter' : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      stubPauseWorldSevm stubPauseWorldAfterSetEntry pauseAfterSet
      (.ok final) := by
    simpa only [stubPauseWorldAfterSetEntry] using hafter
  have reached := stubPauseWorld_afterSetAt hafter'
  have hook := stubBoundaryExecutions_of_afterSet_ok
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (sevm := stubPauseWorldSevm) (entry := stubPauseWorldAfterSetEntry)
    (final := final) (target := pauseWorldCallee)
    (duration := pauseWorldDuration)
    (by rfl) (by rfl) pauseWorld_callee_ne_owner
    stubPauseWorld_target_not_precompile
    (by
      unfold stubPauseWorldAfterSetEntry
      change stubRunAfterSetBase.getCode pauseWorldCallee = _
      rw [← show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
        toAdr_toB256 pauseWorldCallee]
      exact stubRunAfterSetBase_code)
    reached.1 reached.2.1 stubPauseWorld_publicPausePremises.entered
    stubPauseWorld_publicPausePremises.dynamic hafter'
  have conclusion := publicPause_stubPinnedTarget
    stubPauseWorld_publicPausePremises stubPauseWorld_target_ne_owner hprog
    stubPauseWorldAfterSetEntry reached hook final rfl
  refine ⟨stubPauseWorldAfterSetEntry, successPre, final, hprog, reached,
    hsuccess, ?_, hook, conclusion.1, conclusion⟩
  simpa only [stubPauseWorldAfterSetEntry] using hni

end Blanc.LidoCircuitBreaker
