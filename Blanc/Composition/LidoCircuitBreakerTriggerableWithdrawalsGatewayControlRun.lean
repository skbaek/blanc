import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayCrossing

/-!
# Executed closed-world control for the CircuitBreaker × gateway composition

This module replays the production CircuitBreaker public pause from its concrete
entry world and closes the already-proved installed-gateway suffix.  The gas
ladder is derived from the real 15,948-byte gateway crossing rather than copied
from the ten-instruction stub control.
-/

namespace Blanc.Composition

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker
open Blanc.LidoTriggerableWithdrawalsGateway

namespace LidoCircuitBreakerTwg


/-- Both arms of `temporalSloadBase` return the base world with at most the
accessed-key set changed, so the error, output, accessed-address and code
fields all pass through; the named projections below read this one case
split. -/

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



private theorem gatewayRunKeys_expiryBase :
    (pauseExpiryBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256).accessedStorageKeys =
    Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256) := by
  unfold pauseExpiryBase temporalSloadBase
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget,
      assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost gatewayPauseWorldSevm gatewayPauseWorldPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem gatewayRunKeys_durationBase :
    (pauseDurationBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    (Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser) := by
  have hnot : (gatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase gatewayPauseWorldSevm gatewayPauseWorldPre
        pauseWorldCallee.toB256).accessedStorageKeys := by
    rw [gatewayRunKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry
  unfold pauseDurationBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseExpiryBase gatewayPauseWorldSevm gatewayPauseWorldPre
    pauseWorldCallee.toB256).accessedStorageKeys).insert
    (gatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) = _
  rw [gatewayRunKeys_expiryBase]
  rfl

private theorem gatewayRunKeys_kernelBase :
    (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    ((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot) := by
  have hnot : (gatewayPauseWorldSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase gatewayPauseWorldSevm gatewayPauseWorldPre
        pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
    rw [gatewayRunKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm
  unfold pauseKernelBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseDurationBase gatewayPauseWorldSevm gatewayPauseWorldPre
    pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys).insert
    (gatewayPauseWorldSevm.currentTarget, pauseDurationSlot) = _
  rw [gatewayRunKeys_durationBase]
  rfl

private theorem gatewayRunWarm_assign_kernelBase :
    (gatewayPauseWorldSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∈
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
  rw [gatewayRunKeys_kernelBase]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

private theorem gatewayRunKeys_assignPost :
    (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys = (((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)) := by
  show (assignmentBase gatewayPauseWorldSevm (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser)
    pauseWorldCallee.toB256).accessedStorageKeys = _
  unfold assignmentBase temporalSloadBase
  rw [if_pos gatewayRunWarm_assign_kernelBase]
  exact gatewayRunKeys_kernelBase

private theorem gatewayRunKeys_countBase :
    (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys = ((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)) := by
  have hnot : (gatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys := by
    rw [gatewayRunKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count
  unfold temporalSloadBase
  rw [if_neg hnot]
  show ((assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys).insert
    (gatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) = _
  rw [gatewayRunKeys_assignPost]
  rfl

private theorem gatewayRunKeys_removeBase1 :
    (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys = (((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)) := by
  have hnot : (gatewayPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys := by
    show _ ∉ (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [gatewayRunKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee
  rw [temporalSloadBase_cold_keys _ _ _ hnot]
  show ((temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys).insert
    (gatewayPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) = _
  rw [gatewayRunKeys_countBase]
  rfl

private theorem gatewayRunKeys_removeBase2 :
    (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
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
  have hnot : (gatewayPauseWorldSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys := by
    rw [gatewayRunKeys_removeBase1]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_length_ne_indexCallee.symm
    · exact pauseWorld_length_ne_count.symm
    · exact pauseWorld_duration_ne_length
    · exact pauseWorld_length_ne_expiry.symm
    · exact pauseWorld_length_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, gatewayRunKeys_removeBase1]
  rfl

private theorem gatewayRunKeys_removeBase3 :
    (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
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
  have hnot : (gatewayPauseWorldSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys := by
    rw [gatewayRunKeys_removeBase2]
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
  rw [temporalSloadBase_cold_keys _ _ _ hnot, gatewayRunKeys_removeBase2]
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

private theorem gatewayRunCost_assignment :
    temporalSloadCost gatewayPauseWorldSevm (pauseLockPost gatewayPauseWorldSevm gatewayPauseWorldPre)
      (assignmentSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost gatewayPauseWorldSevm gatewayPauseWorldPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem gatewayRunCost_expiry :
    temporalSloadCost gatewayPauseWorldSevm
      (pauseExpiryBase gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256)
      (expirySlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256).accessedStorageKeys from by
    rw [gatewayRunKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry)]
  rfl

private theorem gatewayRunCost_duration :
    temporalSloadCost gatewayPauseWorldSevm
      (pauseDurationBase gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser)
      pauseDurationSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256
        pauseWorldPauser).accessedStorageKeys from by
    rw [gatewayRunKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm)]
  rfl

private theorem gatewayRunCost_assignWarm :
    temporalSloadCost gatewayPauseWorldSevm (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser)
      (assignmentSlot pauseWorldCallee.toB256) = 100 := by
  unfold temporalSloadCost
  rw [if_pos gatewayRunWarm_assign_kernelBase]
  rfl

private theorem gatewayRunCost_countCold :
    temporalSloadCost gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys from by
    rw [gatewayRunKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count)]
  rfl

private theorem gatewayRunCost_idxCold :
    temporalSloadCost gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys from by
    show _ ∉ (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [gatewayRunKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee)]
  rfl

private theorem gatewayRunCost_lenCold :
    temporalSloadCost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys from by
    rw [gatewayRunKeys_removeBase1]
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

private theorem gatewayRunCost_arrCold :
    temporalSloadCost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (gatewayPauseWorldSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys from by
    rw [gatewayRunKeys_removeBase2]
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

private theorem gatewayRunKernelPrefixGas :
    foundSetPauserKernelPrefixGas gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
        pauseWorldCallee.toB256 pauseWorldPauser)
      pauseWorldCallee.toB256 0 pauseWorldPauser 2900 2900 = 8122 := by
  unfold foundSetPauserKernelPrefixGas
  rw [gatewayRunCost_assignWarm, gatewayRunCost_countCold]

private theorem gatewayRunWarm_count_rb3 :
    (gatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [gatewayRunKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))

private theorem gatewayRunWarm_expiry_rb3 :
    (gatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [gatewayRunKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (Std.HashSet.mem_insert.mpr
        (Or.inr Std.HashSet.mem_insert_self)))))))))

/-! ## Storage read through the tower, stage by stage

Each lemma peels exactly one named layer by rewrite, per the substrate's
one-layer transport discipline. -/

private theorem gatewayRunStor_lockPost (key : B256) :
    (pauseLockPost gatewayPauseWorldSevm gatewayPauseWorldPre).getStorVal configWorldOwner key =
      pauseLastWorldStor.get key := by
  show gatewayPauseWorldPre.getStorVal configWorldOwner key = _
  exact gatewayPauseWorld_getStorVal

private theorem gatewayRunStor_kernelBase (key : B256) :
    (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_lockPost key

private theorem gatewayRunStor_assignPost_other {key : B256}
    (h : assignmentSlot pauseWorldCallee.toB256 ≠ key) :
    (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  unfold assignmentPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe h)]
  unfold assignmentBase
  rw [temporalSloadBase_getStorVal]
  exact gatewayRunStor_kernelBase key

private theorem gatewayRunStor_assignPost_self :
    (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  unfold assignmentPost
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_countPost_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hc),
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_assignPost_other ha

private theorem gatewayRunStor_countPost_assign :
    (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
    (keyPairNe pauseWorld_assignCallee_ne_count.symm),
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_assignPost_self

private theorem gatewayRunStor_countPost_count :
    (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 :=
  temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_removeBase3_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_countPost_other ha hc

private theorem gatewayRunStor_removeBase3_count :
    (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_countPost_count

private theorem gatewayRunStor_removeBase3_assign :
    (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_countPost_assign

/-! The five removal-walk writes, peeled from the outside of `B6`:
`indexClearPost` writes the index clear over the length restore, and
`entryClearPost` writes the tail clear over the moved-index and hole
writes. -/

private theorem gatewayRunStor_B6_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key)
    (hr : arrayEntrySlot 1 ≠ key)
    (hi : indexSlot pauseWorldCallee.toB256 ≠ key)
    (hl : arrayLengthSlot ≠ key) :
    (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hl),
    show (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost gatewayPauseWorldSevm
      (indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr),
    show indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr)]
  exact gatewayRunStor_removeBase3_other ha hc

private theorem gatewayRunStor_B6_index :
    (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (indexSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_B6_length :
    (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner arrayLengthSlot = 0 := by
  rw [show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_indexCallee.symm),
    show lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_B6_entry :
    (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (arrayEntrySlot 1) = 0 := by
  rw [show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_indexCallee.symm),
    show lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_entryOne),
    show (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost gatewayPauseWorldSevm
      (indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_B6_assign :
    (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_assignCallee),
    show (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost gatewayPauseWorldSevm
      (indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_assignCallee),
    show indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_assignCallee)]
  exact gatewayRunStor_removeBase3_assign

private theorem gatewayRunStor_B6_count :
    (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_count),
    show (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost gatewayPauseWorldSevm
      (indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count),
    show indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count)]
  exact gatewayRunStor_removeBase3_count

/-! ## The staged memory and its image, through the walk's writes

`pauseMemory`'s five scratch words are staged by the body; the kernel saves
the old pauser at `previousPauserWord`, and the removal walk writes its three
scratch words above it.  Every write stays inside the `768`-byte image, so no
extension is ever charged. -/


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

private theorem gatewayRunAddrs_B7 :
    ((indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨gatewayPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  rw [addLog_accessedAddresses,
    show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost gatewayPauseWorldSevm
      (indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_accessedAddresses,
    show entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
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
  show (assignmentPost gatewayPauseWorldSevm
    (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedAddresses = _
  unfold assignmentPost
  rw [temporalSstorePost_accessedAddresses]
  unfold assignmentBase
  rw [temporalSloadBase_accessedAddresses]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses]
  rfl

private theorem gatewayRunCode_B7 :
    ((indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨gatewayPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = (gatewayCode controlDeployParams) := by
  rw [show ((indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨gatewayPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr from rfl,
    show (indexClearPost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost gatewayPauseWorldSevm
      (lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_getCode,
    show lengthWritePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost gatewayPauseWorldSevm (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_getCode,
    show (entryClearPost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost gatewayPauseWorldSevm
      (indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_getCode,
    show indexWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_getCode,
    show entryWritePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost gatewayPauseWorldSevm
      (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (temporalSstorePost gatewayPauseWorldSevm (temporalSloadBase gatewayPauseWorldSevm (assignmentPost gatewayPauseWorldSevm
      (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
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
  show (assignmentPost gatewayPauseWorldSevm
    (pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr =
    (gatewayCode controlDeployParams)
  unfold assignmentPost
  rw [temporalSstorePost_getCode]
  unfold assignmentBase
  rw [temporalSloadBase_getCode]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getCode, temporalSloadBase_getCode,
    temporalSloadBase_getCode]
  show gatewayPauseWorldPre.state.getCode pauseWorldCallee.toB256.toAdr = (gatewayCode controlDeployParams)
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  exact gatewayPauseWorld_targetCodeAt



private def gatewayRunKernelBase : Devm :=
  pauseKernelBase gatewayPauseWorldSevm gatewayPauseWorldPre
    pauseWorldCallee.toB256 pauseWorldPauser

private def gatewayRunCountPost : Devm :=
  temporalSstorePost gatewayPauseWorldSevm
    (temporalSloadBase gatewayPauseWorldSevm
      (assignmentPost gatewayPauseWorldSevm gatewayRunKernelBase
        pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
    (countSlot pauseWorldPauser) 0

private def gatewayRunRemoveBase3 : Devm :=
  temporalSloadBase gatewayPauseWorldSevm
    (temporalSloadBase gatewayPauseWorldSevm
      (temporalSloadBase gatewayPauseWorldSevm gatewayRunCountPost
        (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
    (arrayEntrySlot 1)

private def gatewayRunAfterSetBase : Devm :=
  (indexClearPost gatewayPauseWorldSevm
    (entryClearPost gatewayPauseWorldSevm gatewayRunRemoveBase3
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0).addLog
      ⟨gatewayPauseWorldSevm.currentTarget,
        [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩

private abbrev gatewayRunMemoryLast : Mem :=
  Blanc.LidoCircuitBreaker.stubRunMemoryLast

private abbrev gatewayRunImageLast : Bytes :=
  Blanc.LidoCircuitBreaker.stubRunImageLast


/-! ## The composed run -/

/-- The row-19 master composition: the boundary walk with its dichotomy
interface facts, and the complete message run with its settled effects. -/

private theorem gatewayPauseWorld_targetPausedZero :
    gatewayPauseWorldPre.getStorVal pauseWorldCallee
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  change (gatewayPauseWorldState.get pauseWorldCallee).stor.get
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0
  rw [gatewayPauseWorldState_get_target]
  rfl

private theorem gatewayPauseWorld_targetPausedOrigZero :
    getOrigStorVal gatewayPauseWorldSevm pauseWorldCallee
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  change (gatewayPauseWorldState.get pauseWorldCallee).stor.get
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0
  rw [gatewayPauseWorldState_get_target]
  rfl

private theorem gatewayPauseWorld_targetPausedCold :
    (pauseWorldCallee, LidoTriggerableWithdrawalsGateway.resumeSinceSlot) ∉
      gatewayPauseWorldPre.accessedStorageKeys := by
  rw [show gatewayPauseWorldPre.accessedStorageKeys =
      Std.HashSet.emptyWithCapacity from rfl]
  exact Std.HashSet.not_mem_emptyWithCapacity

private theorem gatewayRunAfterSetBase_code :
    gatewayRunAfterSetBase.getCode pauseWorldCallee.toB256.toAdr =
      (gatewayCode controlDeployParams) := by
  simpa only [gatewayRunAfterSetBase, gatewayRunRemoveBase3, gatewayRunCountPost,
    gatewayRunKernelBase] using gatewayRunCode_B7

private theorem gatewayRunAfterSetBase_targetKeyCold (key : B256) :
    (pauseWorldCallee.toB256.toAdr, key) ∉
      gatewayRunAfterSetBase.accessedStorageKeys := by
  rw [gatewayRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  unfold gatewayRunRemoveBase3 gatewayRunCountPost gatewayRunKernelBase
  rw [gatewayRunKeys_removeBase3]
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


private theorem gatewayRunAfterSetBase_targetStor (key : B256) :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr key =
      controlGatewayStor.get key := by
  have haddr : pauseWorldCallee.toB256.toAdr ≠
      gatewayPauseWorldSevm.currentTarget := gatewayPauseWorld_target_ne_owner
  unfold gatewayRunAfterSetBase
  rw [addLog_getStorVal]
  unfold indexClearPost lengthWritePost entryClearPost indexWritePost
    entryWritePost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr]
  unfold gatewayRunRemoveBase3
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  unfold gatewayRunCountPost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSloadBase_getStorVal]
  unfold assignmentPost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr]
  unfold assignmentBase gatewayRunKernelBase pauseKernelBase pauseDurationBase
    pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  change (gatewayPauseWorldState.get pauseWorldCallee).stor.get key = _
  rw [gatewayPauseWorldState_get_target]

private theorem gatewayRunAfterSetBase_targetPausedZero :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  rw [gatewayRunAfterSetBase_targetStor]
  rfl

private theorem gatewayRunAfterSetBase_roleIndex :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      (roleLookupIndexSlot pauseRole
        gatewayPauseWorldSevm.currentTarget.toB256) = 1 := by
  rw [gatewayRunAfterSetBase_targetStor, gatewayPauseWorld_currentTarget]
  rfl

private theorem gatewayRunAfterSetBase_role :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      (roleLookupRoleSlot pauseRole
        gatewayPauseWorldSevm.currentTarget.toB256) = pauseRole := by
  rw [gatewayRunAfterSetBase_targetStor, gatewayPauseWorld_currentTarget]
  rfl

private theorem gatewayRunAfterSetBase_account :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      (roleLookupAccountSlot pauseRole
        gatewayPauseWorldSevm.currentTarget.toB256) =
      canonicalAccount gatewayPauseWorldSevm.currentTarget.toB256 := by
  rw [gatewayRunAfterSetBase_targetStor, gatewayPauseWorld_currentTarget]
  decide +kernel

private theorem gatewayRunAfterSetBase_count :
    gatewayRunAfterSetBase.getStorVal configWorldOwner
      (countSlot pauseWorldPauser) = 0 := by
  rw [gatewayRunAfterSetBase, addLog_getStorVal]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    gatewayRunStor_B6_count

private theorem gatewayRunAfterSetBase_interval :
    gatewayRunAfterSetBase.getStorVal configWorldOwner heartbeatIntervalSlot =
      pauseWorldInterval := by
  rw [gatewayRunAfterSetBase, addLog_getStorVal]
  have h := (gatewayRunStor_B6_other
    pauseWorld_interval_ne_assignCallee.symm
    pauseWorld_interval_ne_count.symm
    pauseWorld_interval_ne_entryOne.symm
    pauseWorld_interval_ne_indexCallee.symm
    pauseWorld_interval_ne_length.symm).trans pauseLastStor_interval
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using h

private theorem gatewayRunAfterSetBase_expiry :
    gatewayRunAfterSetBase.getStorVal configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  rw [gatewayRunAfterSetBase, addLog_getStorVal]
  have h := (gatewayRunStor_B6_other pauseWorld_assignCallee_ne_expiry
    pauseWorld_count_ne_expiry pauseWorld_entryOne_ne_expiry
    pauseWorld_indexCallee_ne_expiry pauseWorld_length_ne_expiry).trans
      pauseLastStor_expiry
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using h

private theorem gatewayRunAfterSetBase_accessedAddresses :
    gatewayRunAfterSetBase.accessedAddresses = Std.HashSet.emptyWithCapacity := by
  simpa only [gatewayRunAfterSetBase, gatewayRunRemoveBase3, gatewayRunCountPost,
    gatewayRunKernelBase] using gatewayRunAddrs_B7


private theorem gatewayRunAfterSetBase_warmCount :
    (gatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
      gatewayRunAfterSetBase.accessedStorageKeys := by
  rw [gatewayRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    gatewayRunWarm_count_rb3

private theorem gatewayRunAfterSetBase_warmExpiry :
    (gatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
      gatewayRunAfterSetBase.accessedStorageKeys := by
  rw [gatewayRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    gatewayRunWarm_expiry_rb3

private theorem gatewayRunAfterSetBase_roleIndexCold :
    (pauseWorldCallee.toB256.toAdr,
      roleLookupIndexSlot pauseRole
        gatewayPauseWorldSevm.currentTarget.toB256) ∉
      gatewayRunAfterSetBase.accessedStorageKeys :=
  gatewayRunAfterSetBase_targetKeyCold _

private theorem gatewayRunAfterSetBase_roleCold :
    (pauseWorldCallee.toB256.toAdr,
      roleLookupRoleSlot pauseRole
        gatewayPauseWorldSevm.currentTarget.toB256) ∉
      (addAccessedStorageKey gatewayRunAfterSetBase
        pauseWorldCallee.toB256.toAdr
        (roleLookupIndexSlot pauseRole
          gatewayPauseWorldSevm.currentTarget.toB256)).accessedStorageKeys := by
  rw [addAccessedStorageKey_accessedStorageKeys']
  simp only [Std.HashSet.mem_insert, beq_iff_eq, not_or]
  exact ⟨by decide +kernel, gatewayRunAfterSetBase_targetKeyCold _⟩

private theorem gatewayRunAfterSetBase_accountCold :
    (pauseWorldCallee.toB256.toAdr,
      roleLookupAccountSlot pauseRole
        gatewayPauseWorldSevm.currentTarget.toB256) ∉
      (addAccessedStorageKey
        (addAccessedStorageKey gatewayRunAfterSetBase
          pauseWorldCallee.toB256.toAdr
          (roleLookupIndexSlot pauseRole
            gatewayPauseWorldSevm.currentTarget.toB256))
        pauseWorldCallee.toB256.toAdr
        (roleLookupRoleSlot pauseRole
          gatewayPauseWorldSevm.currentTarget.toB256)).accessedStorageKeys := by
  rw [addAccessedStorageKey_accessedStorageKeys',
    addAccessedStorageKey_accessedStorageKeys']
  simp only [Std.HashSet.mem_insert, beq_iff_eq, not_or]
  exact ⟨by decide +kernel, by decide +kernel,
    gatewayRunAfterSetBase_targetKeyCold _⟩

private theorem gatewayRunAfterSetBase_resumeCold :
    (pauseWorldCallee.toB256.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { gatewayPauseWorldSevm with
          currentTarget := pauseWorldCallee.toB256.toAdr
          caller := gatewayPauseWorldSevm.currentTarget }
        gatewayRunAfterSetBase).accessedStorageKeys := by
  simp only [pauseRoleWarm, addAccessedStorageKey_accessedStorageKeys',
    Std.HashSet.mem_insert, beq_iff_eq, not_or]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    gatewayRunAfterSetBase_targetKeyCold _⟩

private theorem gatewayPauseWorld_afterSetGatewaySeam :
    ∃ mid : Devm,
      mid.stack = [] ∧
      mid.memory = pauseDecodedMemory gatewayRunMemoryLast pauseWorldDuration ∧
      mid.gasLeft = 42343 ∧
      (∀ key : B256,
        mid.getStorVal configWorldOwner key =
          gatewayRunAfterSetBase.getStorVal configWorldOwner key) ∧
      (gatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      (gatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      ∀ final : Devm,
        Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            gatewayPauseWorldSevm mid pauseSuccess final →
          Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            gatewayPauseWorldSevm
            (gatewayRunAfterSetBase.setMach
              ⟨[], gatewayRunMemoryLast, 75328⟩)
            pauseAfterSet final := by
  obtain ⟨mid, hstk, hmem, hgas, _herr, _hout, _hret, _hlogs,
      _hrefund, _hatd, _htrans, hask, _haddrs, _hpaused, hchain, hclose⟩ :=
    pauseAfterSet_gateway_toSuccess_runCompiled
      ((runtime officialParams).main :: (runtime officialParams).aux)
      gatewayPauseWorldSevm gatewayRunAfterSetBase pauseWorldCallee.toB256
      pauseWorldDuration gatewayRunMemoryLast gatewayRunImageLast 2600 42362
      (by simpa only [gatewayRunMemoryLast,
          Blanc.LidoCircuitBreaker.stubRunMemoryLast] using stubRunMem_wfLast)
      (by simpa only [gatewayRunMemoryLast, gatewayRunImageLast,
        Blanc.LidoCircuitBreaker.stubRunMemoryLast,
        Blanc.LidoCircuitBreaker.stubRunImageLast] using
        stubRunMem_readsLast)
      (by simpa only [gatewayRunImageLast,
        Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_targetLast)
      (by simpa only [gatewayRunImageLast,
        Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_durLast)
      (by simpa only [gatewayRunMemoryLast,
        Blanc.LidoCircuitBreaker.stubRunMemoryLast] using stubRunMem_sizeLast)
      (by
        unfold temporalAccountAccessCost
        rw [if_neg (show ¬ pauseWorldCallee.toB256.toAdr ∈
            gatewayRunAfterSetBase.accessedAddresses from by
          rw [gatewayRunAfterSetBase_accessedAddresses]
          exact Std.HashSet.not_mem_emptyWithCapacity)]
        rfl)
      gatewayRunAfterSetBase_code
      gatewayRunAfterSetBase_roleIndex
      gatewayRunAfterSetBase_role
      gatewayRunAfterSetBase_account
      gatewayRunAfterSetBase_roleIndexCold
      gatewayRunAfterSetBase_roleCold
      gatewayRunAfterSetBase_accountCold
      gatewayRunAfterSetBase_targetPausedZero
      (by simpa only [toAdr_toB256] using
        gatewayPauseWorld_targetPausedOrigZero)
      gatewayRunAfterSetBase_resumeCold
      rfl
      (by decide)
      (by decide)
      (by decide)
      (by show (1024 : Nat) ≠ 0; decide)
      (by simpa only [toAdr_toB256] using
        gatewayPauseWorld_target_not_precompile)
      (by norm_num)
      (by
        have hfiniteCost : pauseWorldDuration ≠ pauseInfiniteSentinel := by
          decide +kernel
        simp only [gatewayPauseChildCost, if_neg hfiniteCost]
        norm_num)
  rcases hchain with ⟨st₁, st₂, hsub₁, hsub₂, hstate⟩
  have htargetOwner : pauseWorldCallee.toB256.toAdr ≠
      configWorldOwner := by
    simpa only [gatewayPauseWorld_currentTarget] using
      gatewayPauseWorld_target_ne_owner
  have hownerStor : (mid.state.get configWorldOwner).stor =
      (gatewayRunAfterSetBase.state.get configWorldOwner).stor := by
    rw [hstate]
    have hadd₂ :
        ((st₂.addBal pauseWorldCallee.toB256.toAdr 0).get
          configWorldOwner).stor = (st₂.get configWorldOwner).stor := by
      unfold State.addBal
      exact State.setBal_get_stor
    have hwrite :
        (((st₁.addBal pauseWorldCallee.toB256.toAdr 0).setStorVal
          pauseWorldCallee.toB256.toAdr
          LidoTriggerableWithdrawalsGateway.resumeSinceSlot
          (pauseForProjection gatewayPauseWorldSevm.benvStat.time
            pauseWorldDuration)).get configWorldOwner).stor =
          ((st₁.addBal pauseWorldCallee.toB256.toAdr 0).get
            configWorldOwner).stor := by
      unfold State.setStorVal
      exact congrArg Acct.stor (State.get_set_ne _ htargetOwner _)
    have hadd₁ :
        ((st₁.addBal pauseWorldCallee.toB256.toAdr 0).get
          configWorldOwner).stor = (st₁.get configWorldOwner).stor := by
      unfold State.addBal
      exact State.setBal_get_stor
    exact hadd₂.trans ((Blanc.state_subBal_stor hsub₂).trans
      (hwrite.trans (hadd₁.trans (Blanc.state_subBal_stor hsub₁))))
  have hstor : ∀ key : B256,
      mid.getStorVal configWorldOwner key =
        gatewayRunAfterSetBase.getStorVal configWorldOwner key := by
    intro key
    exact congrArg (fun stor => stor.get key) hownerStor
  refine ⟨mid, hstk, hmem, hgas, hstor,
    (hask _).mpr (Std.HashSet.mem_union_iff.mpr
      (Or.inl gatewayRunAfterSetBase_warmCount)),
    (hask _).mpr (Std.HashSet.mem_union_iff.mpr
      (Or.inl gatewayRunAfterSetBase_warmExpiry)), ?_⟩
  intro final hrun
  have h := hclose final hrun
  have hfiniteCost : pauseWorldDuration ≠ pauseInfiniteSentinel := by
    decide +kernel
  simp only [gatewayPauseChildCost, if_neg hfiniteCost] at h
  rw [show (42362 + 29772 + 594 + 2600 : Nat) = 75328 from by norm_num] at h
  exact h

private theorem gatewayPauseWorld_originalExpiry :
    getOrigStorVal gatewayPauseWorldSevm configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  change (gatewayPauseWorldState.get configWorldOwner).stor.get
    (expirySlot pauseWorldPauser) = pauseWorldExpiry
  rw [gatewayPauseWorldState_get_breaker]
  exact pauseLastStor_expiry

private def gatewayRunDecodedMemory : Mem :=
  pauseDecodedMemory gatewayRunMemoryLast pauseWorldDuration

private def gatewayRunImage8 : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt gatewayRunImageLast 256 pauseForSelector.toBytes)
        288 pauseWorldDuration.toBytes)
      256 isPausedSelector.toBytes)
    0 (1 : B256).toBytes

private def gatewayRunAfterSetNoLog : Devm :=
  indexClearPost gatewayPauseWorldSevm
    (entryClearPost gatewayPauseWorldSevm gatewayRunRemoveBase3
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0

private def gatewayRunMemory1 : Mem :=
  (pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

private def gatewayRunImage1 : Bytes :=
  Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

private theorem gatewayPauseWorld_getOrigStorVal (key : B256) :
    getOrigStorVal gatewayPauseWorldSevm configWorldOwner key =
      pauseLastWorldStor.get key := by
  change (gatewayPauseWorldState.get configWorldOwner).stor.get key = _
  rw [gatewayPauseWorldState_get_breaker]

private theorem gatewayPauseWorld_successSuffix :
    ∃ successPre final : Devm,
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm successPre pauseSuccess final ∧
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm
          (gatewayRunAfterSetBase.setMach
            ⟨[], gatewayRunMemoryLast, 75328⟩)
          pauseAfterSet final ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm
          (gatewayRunAfterSetBase.setMach
            ⟨[], gatewayRunMemoryLast, 75328⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference gatewayPauseWorldSevm
        (gatewayRunAfterSetBase.setMach
          ⟨[], gatewayRunMemoryLast, 75328⟩) successPre := by
  obtain ⟨mid, hstk, hmem, hgas, hstor, hwarmCount, hwarmExpiry, hclose⟩ :=
    gatewayPauseWorld_afterSetGatewaySeam
  have hmidCount : mid.getStorVal gatewayPauseWorldSevm.currentTarget
      (countSlot pauseWorldPauser) = 0 := by
    rw [gatewayPauseWorld_currentTarget, hstor]
    exact gatewayRunAfterSetBase_count
  have hmidExpiry : mid.getStorVal gatewayPauseWorldSevm.currentTarget
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
    rw [gatewayPauseWorld_currentTarget, hstor]
    exact gatewayRunAfterSetBase_expiry
  have hW8 := pauseSuccess_zeroCount_ok_runCompiled
    ((runtime officialParams).main :: (runtime officialParams).aux)
    gatewayPauseWorldSevm mid gatewayRunDecodedMemory gatewayRunImage8
    pauseWorldCallee.toB256 pauseWorldDuration pauseWorldPauser
    pauseWorldExpiry pauseWorldExpiry 100 2900 36021
    (by simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast,
      Blanc.LidoCircuitBreaker.stubRunMemoryLast] using
      stubRunMem_wf8)
    (by simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast, gatewayRunImage8,
      gatewayRunImageLast, Blanc.LidoCircuitBreaker.stubRunMemoryLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_reads8)
    (by simpa only [gatewayRunImage8, gatewayRunImageLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using
      stubRunMem_target8)
    (by simpa only [gatewayRunImage8, gatewayRunImageLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_dur8)
    (by
      rw [gatewayRunDecodedMemory, gatewayRunMemoryLast,
        Blanc.LidoCircuitBreaker.stubRunMemoryLast, stubRunMem_size8])
    (by
      rw [gatewayRunDecodedMemory, gatewayRunMemoryLast,
        Blanc.LidoCircuitBreaker.stubRunMemoryLast, stubRunMem_size8])
    gatewayPauseWorld_callerWord hmidCount
    (by
      unfold temporalSloadCost
      rw [if_pos hwarmCount]
      rfl)
    hmidExpiry
    (by
      rw [gatewayPauseWorld_currentTarget]
      exact gatewayPauseWorld_originalExpiry)
    hwarmExpiry
    (stubRunSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend])
    rfl
  have hmidEta : mid.setMach
      ⟨[], gatewayRunDecodedMemory, 36021 + 3322 + 100 + 2900⟩ = mid := by
    rw [show (36021 + 3322 + 100 + 2900 : Nat) = 42343 from by norm_num,
      gatewayRunDecodedMemory, ← hgas, ← hmem, ← hstk]
    rfl
  rw [hmidEta] at hW8
  have hafter := hclose _ hW8
  have hboundary := Func.RunCompiledTo.of_runCompiled hW8
  have hafterTo := Func.RunCompiledTo.of_runCompiled hafter
  refine ⟨mid, _, hW8, hafter, hboundary, hafterTo, ?_⟩
  unfold PauseSuccessNoninterference
  rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_callerWord]
  constructor
  · rw [hstor, setMach_getStorVal]
  · rw [hstor, setMach_getStorVal]

private theorem gatewayPauseWorld_productionRun :
    ∃ successPre final : Devm,
      Prog.RunCompiledTo gatewayPauseWorldSevm gatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm
          (gatewayRunAfterSetBase.setMach
            ⟨[], gatewayRunMemoryLast, 75328⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference gatewayPauseWorldSevm
        (gatewayRunAfterSetBase.setMach
          ⟨[], gatewayRunMemoryLast, 75328⟩) successPre := by
  obtain ⟨successPre, final, hsuccess, hafter, hsuccessTo, hafterTo, hni⟩ :=
    gatewayPauseWorld_successSuffix
  have hfin := finishSetPauser_pauseAfterSet_runCompiled officialParams
    gatewayPauseWorldSevm gatewayRunAfterSetNoLog gatewayRunMemoryLast gatewayRunImageLast
    pauseWorldCallee.toB256 pauseWorldPauser 0 [] 75328 _ (by decide)
    (by simpa only [gatewayRunMemoryLast, gatewayRunImageLast,
      Blanc.LidoCircuitBreaker.stubRunMemoryLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using
      stubRunMem_readsLast)
    (by simpa only [gatewayRunImageLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_targetLast)
    (by simpa only [gatewayRunImageLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_prevLast)
    (by simpa only [gatewayRunImageLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_newLast)
    (by simpa only [gatewayRunImageLast,
      Blanc.LidoCircuitBreaker.stubRunImageLast] using stubRunMem_contLast)
    (by rw [gatewayRunMemoryLast,
      Blanc.LidoCircuitBreaker.stubRunMemoryLast, stubRunMem_sizeLast]; decide)
    (by rw [gatewayRunMemoryLast,
      Blanc.LidoCircuitBreaker.stubRunMemoryLast, stubRunMem_sizeLast])
    rfl
    (by
      simpa only [gatewayRunAfterSetNoLog, gatewayRunAfterSetBase,
        gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using hafter)
  rw [show (75328 + 1934 : Nat) = 77262 from by norm_num] at hfin
  have hrem := removeTarget_toFinish_coldEntry_runCompiled officialParams
    gatewayPauseWorldSevm gatewayRunCountPost gatewayRunMemory1 gatewayRunImage1
    pauseWorldCallee.toB256 0 1 [] (by decide)
    pauseWorldCallee.toB256 1 1
    2100 2100 2100 100 100 2900 2900 2900 77262 0
    (by simpa only [gatewayRunMemory1] using stubRunMem_wf1)
    (by simpa only [gatewayRunMemory1, gatewayRunImage1] using stubRunMem_reads1)
    (by simpa only [gatewayRunImage1] using stubRunMem_target1)
    pauseWorld_calleeValid
    (by decide) (by decide) 768 0 0 0
    (by simpa only [gatewayRunMemory1] using stubRunMem_size1)
    (by rw [gatewayRunMemory1, stubRunMem_size1])
    (by decide) (by decide) (by decide) (by decide)
    ((gatewayRunStor_countPost_other
      pauseWorld_entryOne_ne_assignCallee.symm
      pauseWorld_entryOne_ne_count.symm).trans pauseLastStor_entry)
    ((gatewayRunStor_countPost_other pauseWorld_assignCallee_ne_indexCallee
      pauseWorld_indexCallee_ne_count.symm).trans pauseLastStor_index)
    ((gatewayRunStor_countPost_other pauseWorld_length_ne_assignCallee.symm
      pauseWorld_length_ne_count.symm).trans pauseLastStor_length)
    ((gatewayPauseWorld_getOrigStorVal _).trans pauseLastStor_entry)
    ((gatewayPauseWorld_getOrigStorVal _).trans pauseLastStor_index)
    ((gatewayPauseWorld_getOrigStorVal _).trans pauseLastStor_length)
    gatewayRunCost_idxCold gatewayRunCost_lenCold gatewayRunCost_arrCold
    stubRunSvc_noop stubRunSvc_noop
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (by decide) (by norm_num [gCallStipend]) rfl _
    (by dsimp only; exact hfin)
  rw [show (0 + 77262 + 139 + 0 + 0 + 0 + 2100 + 2100 + 2100 + 100 +
    100 + 2900 + 2900 + 2900 : Nat) = 92601 from by norm_num] at hrem
  have hglue := afterOldPauser_removeTarget_runCompiled officialParams
    gatewayPauseWorldSevm gatewayRunCountPost gatewayRunMemory1 gatewayRunImage1 []
    92601 _ (by decide)
    (by simpa only [gatewayRunMemory1, gatewayRunImage1] using stubRunMem_reads1)
    (by simpa only [gatewayRunImage1] using stubRunMem_new1)
    (by rw [gatewayRunMemory1, stubRunMem_size1]; decide)
    (by rw [gatewayRunMemory1, stubRunMem_size1])
    hrem
  rw [show (92601 + 35 : Nat) = 92636 from by norm_num] at hglue
  have hker := setPauserKernel_found_runCompiled officialParams
    gatewayPauseWorldSevm gatewayRunKernelBase
    (pauseMemory pauseWorldCallee.toB256 pauseWorldDuration)
    (pauseImage pauseWorldCallee.toB256 pauseWorldDuration) _
    pauseWorldCallee.toB256 0 pauseWorldPauser 1 pauseWorldPauser 1
    2900 2900 92636 0
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
    ((gatewayRunStor_kernelBase _).trans pauseLastStor_assignment)
    ((gatewayPauseWorld_getOrigStorVal _).trans pauseLastStor_assignment)
    (stubRunSvc_reset (by decide) (by decide))
    ((gatewayRunStor_assignPost_other pauseWorld_assignCallee_ne_count).trans
      pauseLastStor_count)
    ((gatewayPauseWorld_getOrigStorVal _).trans pauseLastStor_count)
    (stubRunSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend]) rfl
    (by
      dsimp only [gatewayRunKernelBase, gatewayRunCountPost, gatewayRunMemory1,
        gatewayRunImage1]
      rw [show (1 - 1 : B256) = 0 from by decide]
      exact hglue)
  rw [show foundSetPauserKernelPrefixGas gatewayPauseWorldSevm
      gatewayRunKernelBase pauseWorldCallee.toB256 0 pauseWorldPauser
      2900 2900 = 8122 from by
        simpa only [gatewayRunKernelBase] using gatewayRunKernelPrefixGas,
    show (0 + 92636 + 8122 : Nat) = 100758 from by norm_num] at hker
  have hcalldata := pauseCalldata_facts
    gatewayPauseWorld_publicPausePremises.calldata
  have hbody := pause_body_runCompiled officialParams gatewayPauseWorldSevm
    gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser
    pauseWorldExpiry pauseWorldDuration 2100 2100 2100 100758 _
    hcalldata.1
    (by decide) rfl
    hcalldata.2
    gatewayPauseWorld_callerWord
    ((gatewayRunStor_lockPost _).trans pauseLastStor_assignment)
    gatewayRunCost_assignment
    (by
      unfold pauseExpiryBase
      rw [temporalSloadBase_getStorVal]
      exact (gatewayRunStor_lockPost _).trans pauseLastStor_expiry)
    gatewayRunCost_expiry
    (by decide)
    (by
      unfold pauseDurationBase pauseExpiryBase
      rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
      exact (gatewayRunStor_lockPost _).trans pauseLastStor_duration)
    gatewayRunCost_duration rfl hker
  rw [show (100758 + (469 + 2100 + 2100 + 2100) : Nat) = 107527 from by
    norm_num] at hbody
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  obtain ⟨hprog, _hcompile⟩ := pause_dispatch_runCompiledTo officialParams
    gatewayPauseWorldSevm gatewayPauseWorldPre 107527 0 _
    hcalldata.1
    gatewayPauseWorld_publicPausePremises.valueZero
    gatewayPauseWorld_publicPausePremises.selectorEq
    (by
      rw [gatewayPauseWorld_publicPausePremises.currentTarget]
      exact gatewayPauseWorld_publicPausePremises.codeAddress)
    gatewayPauseWorld_publicPausePremises.productionBytes hbodyTo
  have hentry : gatewayPauseWorldPre.setMach
      ⟨[], Mem.empty, 0 + pauseDispatchGas + 107527⟩ =
      gatewayPauseWorldPre := by
    rw [show (0 + pauseDispatchGas + 107527 : Nat) = gatewayPauseWorldGas from by
      norm_num [pauseDispatchGas, gatewayPauseWorldGas]]
    rfl
  rw [hentry] at hprog
  exact ⟨successPre, final, hprog, hsuccessTo, hafterTo, hni⟩

private def gatewayPauseWorldAfterSetEntry : Devm :=
  gatewayRunAfterSetBase.setMach ⟨[], gatewayRunMemoryLast, 75328⟩

private theorem gatewayPauseWorldAfterSetEntry_memory :
    gatewayPauseWorldAfterSetEntry.memory = gatewayRunMemoryLast := by
  rw [gatewayPauseWorldAfterSetEntry, Devm.memory_setMach]

private theorem gatewayRunMemoryLast_wf : Mem.Wf gatewayRunMemoryLast := by
  unfold gatewayRunMemoryLast
  exact stubRunMem_wfLast

private theorem gatewayRunMemoryLast_reads :
    Mem.Reads gatewayRunMemoryLast gatewayRunImageLast := by
  unfold gatewayRunMemoryLast gatewayRunImageLast
  exact stubRunMem_readsLast

private theorem gatewayRunImageLast_target :
    Bytes.toB256
      (gatewayRunImageLast.sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  unfold gatewayRunImageLast
  exact stubRunMem_targetLast

private theorem gatewayRunImageLast_duration :
    Bytes.toB256
      (gatewayRunImageLast.sliceD (durationWord * 32).toNat 32 0) =
      pauseWorldDuration := by
  unfold gatewayRunImageLast
  exact stubRunMem_durLast

private theorem gatewayRunMemoryLast_targetWindow {devm : Devm}
    (hmemory : devm.memory = gatewayRunMemoryLast) :
    MemWordAt devm (targetWord * 32).toNat pauseWorldCallee.toB256 := by
  unfold MemWordAt
  rw [hmemory]
  refine ⟨gatewayRunMemoryLast_wf, gatewayRunImageLast,
    gatewayRunMemoryLast_reads, ?_⟩
  have hlen :
      (gatewayRunImageLast.sliceD (targetWord * 32).toNat 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rw [← gatewayRunImageLast_target, Bytes.toBytes_toB256_of_length hlen]

private theorem gatewayRunMemoryLast_durationWindow {devm : Devm}
    (hmemory : devm.memory = gatewayRunMemoryLast) :
    MemWordAt devm (durationWord * 32).toNat pauseWorldDuration := by
  unfold MemWordAt
  rw [hmemory]
  refine ⟨gatewayRunMemoryLast_wf, gatewayRunImageLast,
    gatewayRunMemoryLast_reads, ?_⟩
  have hlen :
      (gatewayRunImageLast.sliceD (durationWord * 32).toNat 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rw [← gatewayRunImageLast_duration, Bytes.toBytes_toB256_of_length hlen]

private theorem gatewayPauseWorld_afterSetAt {final : Devm}
    (hafter : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      gatewayPauseWorldSevm gatewayPauseWorldAfterSetEntry pauseAfterSet
      (.ok final)) :
    PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256
      pauseWorldDuration (gatewayCode controlDeployParams) (.ok final)
      gatewayPauseWorldAfterSetEntry := by
  refine ⟨?_, ?_, ?_, ?_, hafter⟩
  · exact gatewayRunMemoryLast_targetWindow
      gatewayPauseWorldAfterSetEntry_memory
  · exact gatewayRunMemoryLast_durationWindow
      gatewayPauseWorldAfterSetEntry_memory
  · unfold CodeAt gatewayPauseWorldAfterSetEntry
    change gatewayRunAfterSetBase.getCode pauseWorldCallee.toB256.toAdr = _
    exact gatewayRunAfterSetBase_code
  · rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_callerWord]
    unfold gatewayPauseWorldAfterSetEntry
    rw [setMach_getStorVal, gatewayRunAfterSetBase_count,
      gatewayPauseWorld_getStorVal, pauseLastStor_count]
    decide

/-- A concrete production public pause with the installed pinned-target gateway.
The theorem exposes the production run, exact `pauseAfterSet` entry, actual
`pauseSuccess` subrun, explicit callback noninterference, combined hook,
committed outcome family, and the final pinned-target conclusion. -/
theorem gatewayPauseWorld_closedPublicPause :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo gatewayPauseWorldSevm gatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256
          pauseWorldDuration (gatewayCode controlDeployParams) (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference gatewayPauseWorldSevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm entry pauseWorldCallee
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams) pauseWorldDuration (.ok final) ∧
      PublicPauseCommittedOutcomes gatewayPauseWorldSevm gatewayPauseWorldPre
          pauseWorldCallee.toB256 pauseWorldDuration
          (gatewayCode controlDeployParams) (.ok final) ∧
      PublicPausePinnedTargetConclusion gatewayPauseWorldSevm
          gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldDuration
          (gatewayCode controlDeployParams) (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          LidoTriggerableWithdrawalsGateway.pausedUntil (.ok final) final := by
  obtain ⟨successPre, final, hprog, hsuccess, hafter, hni⟩ :=
    gatewayPauseWorld_productionRun
  have hafter' : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      gatewayPauseWorldSevm gatewayPauseWorldAfterSetEntry pauseAfterSet
      (.ok final) := by
    simpa only [gatewayPauseWorldAfterSetEntry] using hafter
  have reached := gatewayPauseWorld_afterSetAt hafter'
  have hook := gatewayBoundaryExecutions_of_afterSet_ok
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (sevm := gatewayPauseWorldSevm) (entry := gatewayPauseWorldAfterSetEntry)
    (final := final) (target := pauseWorldCallee)
    (duration := pauseWorldDuration)
    (by rfl) (by rfl) pauseWorld_callee_ne_owner
    gatewayPauseWorld_target_not_precompile
    (by
      unfold gatewayPauseWorldAfterSetEntry
      change gatewayRunAfterSetBase.getCode pauseWorldCallee = _
      rw [← show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
        toAdr_toB256 pauseWorldCallee]
      exact gatewayRunAfterSetBase_code)
    reached.1 reached.2.1 gatewayPauseWorld_publicPausePremises.dynamic hafter'
  have conclusion := gatewayPauseWorld_closedPremises hprog rfl
  refine ⟨gatewayPauseWorldAfterSetEntry, successPre, final, hprog, reached,
    hsuccess, ?_, hook, conclusion.1, conclusion⟩
  simpa only [gatewayPauseWorldAfterSetEntry] using hni

end LidoCircuitBreakerTwg

end Blanc.Composition
