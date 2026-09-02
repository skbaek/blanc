import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewaySentinelControl

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
open Blanc.Composition.LidoCircuitBreakerTwg

namespace LidoCircuitBreakerTwgSentinel


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
    (pauseExpiryBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256).accessedStorageKeys =
    Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256) := by
  unfold pauseExpiryBase temporalSloadBase
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget,
      assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem gatewayRunKeys_durationBase :
    (pauseDurationBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    (Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser) := by
  have hnot : (sentinelGatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
        pauseWorldCallee.toB256).accessedStorageKeys := by
    rw [gatewayRunKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry
  unfold pauseDurationBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseExpiryBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
    pauseWorldCallee.toB256).accessedStorageKeys).insert
    (sentinelGatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) = _
  rw [gatewayRunKeys_expiryBase]
  rfl

private theorem gatewayRunKeys_kernelBase :
    (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    ((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot) := by
  have hnot : (sentinelGatewayPauseWorldSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
  show ((pauseDurationBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
    pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys).insert
    (sentinelGatewayPauseWorldSevm.currentTarget, pauseDurationSlot) = _
  rw [gatewayRunKeys_durationBase]
  rfl

private theorem gatewayRunWarm_assign_kernelBase :
    (sentinelGatewayPauseWorldSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∈
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
  rw [gatewayRunKeys_kernelBase]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

private theorem gatewayRunKeys_assignPost :
    (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys = (((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)) := by
  show (assignmentBase sentinelGatewayPauseWorldSevm (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser)
    pauseWorldCallee.toB256).accessedStorageKeys = _
  unfold assignmentBase temporalSloadBase
  rw [if_pos gatewayRunWarm_assign_kernelBase]
  exact gatewayRunKeys_kernelBase

private theorem gatewayRunKeys_countBase :
    (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys = ((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)) := by
  have hnot : (sentinelGatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
  show ((assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys).insert
    (sentinelGatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) = _
  rw [gatewayRunKeys_assignPost]
  rfl

private theorem gatewayRunKeys_removeBase1 :
    (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys = (((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)) := by
  have hnot : (sentinelGatewayPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys := by
    show _ ∉ (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
  show ((temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys).insert
    (sentinelGatewayPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) = _
  rw [gatewayRunKeys_countBase]
  rfl

private theorem gatewayRunKeys_removeBase2 :
    (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
  have hnot : (sentinelGatewayPauseWorldSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
  have hnot : (sentinelGatewayPauseWorldSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    temporalSloadCost sentinelGatewayPauseWorldSevm (pauseLockPost sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre)
      (assignmentSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem gatewayRunCost_expiry :
    temporalSloadCost sentinelGatewayPauseWorldSevm
      (pauseExpiryBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256)
      (expirySlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256).accessedStorageKeys from by
    rw [gatewayRunKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry)]
  rfl

private theorem gatewayRunCost_duration :
    temporalSloadCost sentinelGatewayPauseWorldSevm
      (pauseDurationBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser)
      pauseDurationSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256
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
    temporalSloadCost sentinelGatewayPauseWorldSevm (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser)
      (assignmentSlot pauseWorldCallee.toB256) = 100 := by
  unfold temporalSloadCost
  rw [if_pos gatewayRunWarm_assign_kernelBase]
  rfl

private theorem gatewayRunCost_countCold :
    temporalSloadCost sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    temporalSloadCost sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys from by
    show _ ∉ (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    temporalSloadCost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    temporalSloadCost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (sentinelGatewayPauseWorldSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    foundSetPauserKernelPrefixGas sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
        pauseWorldCallee.toB256 pauseWorldPauser)
      pauseWorldCallee.toB256 0 pauseWorldPauser 2900 2900 = 8122 := by
  unfold foundSetPauserKernelPrefixGas
  rw [gatewayRunCost_assignWarm, gatewayRunCost_countCold]

private theorem gatewayRunWarm_count_rb3 :
    (sentinelGatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    (sentinelGatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    (pauseLockPost sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre).getStorVal configWorldOwner key =
      sentinelPauseWorldStor.get key := by
  show sentinelGatewayPauseWorldPre.getStorVal configWorldOwner key = _
  exact sentinelGatewayPauseWorld_getStorVal

private theorem gatewayRunStor_kernelBase (key : B256) :
    (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser).getStorVal configWorldOwner key = sentinelPauseWorldStor.get key := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_lockPost key

private theorem gatewayRunStor_assignPost_other {key : B256}
    (h : assignmentSlot pauseWorldCallee.toB256 ≠ key) :
    (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = sentinelPauseWorldStor.get key := by
  unfold assignmentPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe h)]
  unfold assignmentBase
  rw [temporalSloadBase_getStorVal]
  exact gatewayRunStor_kernelBase key

private theorem gatewayRunStor_assignPost_self :
    (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  unfold assignmentPost
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_countPost_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner key = sentinelPauseWorldStor.get key := by
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hc),
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_assignPost_other ha

private theorem gatewayRunStor_countPost_assign :
    (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
    (keyPairNe pauseWorld_assignCallee_ne_count.symm),
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_assignPost_self

private theorem gatewayRunStor_countPost_count :
    (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 :=
  temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_removeBase3_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner key = sentinelPauseWorldStor.get key := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact gatewayRunStor_countPost_other ha hc

private theorem gatewayRunStor_removeBase3_count :
    (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = sentinelPauseWorldStor.get key := by
  rw [show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hl),
    show (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr),
    show indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr)]
  exact gatewayRunStor_removeBase3_other ha hc

private theorem gatewayRunStor_B6_index :
    (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (indexSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_B6_length :
    (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner arrayLengthSlot = 0 := by
  rw [show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_indexCallee.symm),
    show lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_B6_entry :
    (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (arrayEntrySlot 1) = 0 := by
  rw [show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_indexCallee.symm),
    show lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_entryOne),
    show (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_B6_assign :
    (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_assignCallee),
    show (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_assignCallee),
    show indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_count),
    show (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count),
    show indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
    ((indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨sentinelGatewayPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  rw [addLog_accessedAddresses,
    show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_accessedAddresses,
    show entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
  show (assignmentPost sentinelGatewayPauseWorldSevm
    (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedAddresses = _
  unfold assignmentPost
  rw [temporalSstorePost_accessedAddresses]
  unfold assignmentBase
  rw [temporalSloadBase_accessedAddresses]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses]
  rfl

private theorem gatewayRunCode_B7 :
    ((indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨sentinelGatewayPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = (gatewayCode controlDeployParams) := by
  rw [show ((indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨sentinelGatewayPauseWorldSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr from rfl,
    show (indexClearPost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_getCode,
    show lengthWritePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost sentinelGatewayPauseWorldSevm (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_getCode,
    show (entryClearPost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost sentinelGatewayPauseWorldSevm
      (indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_getCode,
    show indexWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_getCode,
    show entryWritePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost sentinelGatewayPauseWorldSevm
      (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (temporalSstorePost sentinelGatewayPauseWorldSevm (temporalSloadBase sentinelGatewayPauseWorldSevm (assignmentPost sentinelGatewayPauseWorldSevm
      (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
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
  show (assignmentPost sentinelGatewayPauseWorldSevm
    (pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr =
    (gatewayCode controlDeployParams)
  unfold assignmentPost
  rw [temporalSstorePost_getCode]
  unfold assignmentBase
  rw [temporalSloadBase_getCode]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getCode, temporalSloadBase_getCode,
    temporalSloadBase_getCode]
  show sentinelGatewayPauseWorldPre.state.getCode pauseWorldCallee.toB256.toAdr = (gatewayCode controlDeployParams)
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  exact sentinelGatewayPauseWorld_targetCodeAt



private def gatewayRunKernelBase : Devm :=
  pauseKernelBase sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
    pauseWorldCallee.toB256 pauseWorldPauser

private def gatewayRunCountPost : Devm :=
  temporalSstorePost sentinelGatewayPauseWorldSevm
    (temporalSloadBase sentinelGatewayPauseWorldSevm
      (assignmentPost sentinelGatewayPauseWorldSevm gatewayRunKernelBase
        pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
    (countSlot pauseWorldPauser) 0

private def gatewayRunRemoveBase3 : Devm :=
  temporalSloadBase sentinelGatewayPauseWorldSevm
    (temporalSloadBase sentinelGatewayPauseWorldSevm
      (temporalSloadBase sentinelGatewayPauseWorldSevm gatewayRunCountPost
        (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
    (arrayEntrySlot 1)

private def gatewayRunAfterSetBase : Devm :=
  (indexClearPost sentinelGatewayPauseWorldSevm
    (entryClearPost sentinelGatewayPauseWorldSevm gatewayRunRemoveBase3
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0).addLog
      ⟨sentinelGatewayPauseWorldSevm.currentTarget,
        [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩

private def gatewayRunMemoryLast : Mem :=
  ((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
    (removedIndexWord * 32).toNat (1 : B256).toBytes).write
    (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
    (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes

private def gatewayRunImageLast : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt (pauseImage pauseWorldCallee.toB256
            pauseInfiniteSentinel)
          (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
        (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
    (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes

theorem sentinelRunMem_wf1 : Mem.Wf ((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseInfiniteSentinel with ⟨hwf, -⟩
  exact hwf.write _ _

/-- The stage-one facts of the kernel-saved memory, read off
`pauseMemory_spec` in one destructuring: the written image, the unmoved `768`
size, and the two staged words the kernel's write must not disturb.  The four
named facts below are its projections. -/
private theorem sentinelRunMem_stage1 :
    Mem.Reads ((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) ∧
    ((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 ∧
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD
        (targetWord * 32).toNat 32 0) = pauseWorldCallee.toB256 ∧
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD
        (newPauserWord * 32).toNat 32 0) = 0 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseInfiniteSentinel with
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

theorem sentinelRunMem_reads1 : Mem.Reads ((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) :=
  sentinelRunMem_stage1.1

theorem sentinelRunMem_size1 : ((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 :=
  sentinelRunMem_stage1.2.1

theorem sentinelRunMem_target1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 :=
  sentinelRunMem_stage1.2.2.1

theorem sentinelRunMem_new1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
  sentinelRunMem_stage1.2.2.2

theorem sentinelRunMem_wfLast : Mem.Wf (((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  ((sentinelRunMem_wf1.write _ _).write _ _).write _ _

theorem sentinelRunMem_readsLast : Mem.Reads (((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  Mem.Reads.write ((sentinelRunMem_wf1.write _ _).write _ _)
    (Mem.Reads.write (sentinelRunMem_wf1.write _ _)
      (Mem.Reads.write sentinelRunMem_wf1 sentinelRunMem_reads1 _ _) _ _) _ _

private theorem sentinelRunMem_sizeIdx : (((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, sentinelRunMem_size1]
    decide)]
  exact sentinelRunMem_size1

private theorem sentinelRunMem_sizeLen : ((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, sentinelRunMem_sizeIdx]
    decide)]
  exact sentinelRunMem_sizeIdx

theorem sentinelRunMem_sizeLast : (((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, sentinelRunMem_sizeLen]
    decide)]
  exact sentinelRunMem_sizeLen

theorem sentinelRunMem_targetLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact sentinelRunMem_target1

theorem sentinelRunMem_newLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact sentinelRunMem_new1

/-- The three scratch words of the four-write image no later write disturbs,
in one bundle: the saved pauser survives at its own offset below every later
write, and the continuation and duration words sit above them all.  The three
named facts below are its projections. -/
private theorem sentinelRunMem_lastWords :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser ∧
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 ∧
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (durationWord * 32).toNat 32 0) =
      pauseInfiniteSentinel := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseInfiniteSentinel with
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

theorem sentinelRunMem_prevLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser :=
  sentinelRunMem_lastWords.1

theorem sentinelRunMem_contLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 :=
  sentinelRunMem_lastWords.2.1

theorem sentinelRunMem_durLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (durationWord * 32).toNat 32 0) =
      pauseInfiniteSentinel :=
  sentinelRunMem_lastWords.2.2
/-! ## Staged-memory sizes past the crossings -/

private theorem sentinelRunMem_sizeStaged1 : ((((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, sentinelRunMem_sizeLast]
    decide)]
  exact sentinelRunMem_sizeLast

private theorem sentinelRunMem_sizeStaged2 : (((((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseInfiniteSentinel.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, sentinelRunMem_sizeStaged1]
    decide)]
  exact sentinelRunMem_sizeStaged1

private theorem sentinelRunMem_sizeStaged3 : ((((((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseInfiniteSentinel.toBytes).write 256 isPausedSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, sentinelRunMem_sizeStaged2]
    decide)]
  exact sentinelRunMem_sizeStaged2


theorem sentinelRunMem_size8 :
    (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseInfiniteSentinel).size = 768 := by
  unfold pauseDecodedMemory pauseStagedMemory
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, sentinelRunMem_sizeStaged3]
    decide)]
  exact sentinelRunMem_sizeStaged3
theorem sentinelRunMem_wf8 :
    Mem.Wf (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseInfiniteSentinel) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact (((sentinelRunMem_wfLast.write _ _).write _ _).write _ _).write _ _

theorem sentinelRunMem_reads8 :
    Mem.Reads (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseInfiniteSentinel) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 pauseInfiniteSentinel.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact Mem.Reads.write (((sentinelRunMem_wfLast.write _ _).write _ _).write _ _)
    (Mem.Reads.write ((sentinelRunMem_wfLast.write _ _).write _ _)
      (Mem.Reads.write (sentinelRunMem_wfLast.write _ _)
        (Mem.Reads.write sentinelRunMem_wfLast sentinelRunMem_readsLast _ _) _ _) _ _) _ _

theorem sentinelRunMem_target8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 pauseInfiniteSentinel.toBytes) 256
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
  exact sentinelRunMem_targetLast

theorem sentinelRunMem_dur8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 pauseInfiniteSentinel.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes).sliceD (durationWord * 32).toNat 32 0) =
      pauseInfiniteSentinel := by
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
  exact sentinelRunMem_durLast



/-! ## The composed run -/

/-- The row-19 master composition: the boundary walk with its dichotomy
interface facts, and the complete message run with its settled effects. -/

private theorem sentinelGatewayPauseWorld_targetPausedZero :
    sentinelGatewayPauseWorldPre.getStorVal pauseWorldCallee
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  change (sentinelGatewayPauseWorldState.get pauseWorldCallee).stor.get
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0
  rw [sentinelGatewayPauseWorldState_get_target]
  rfl

private theorem sentinelGatewayPauseWorld_targetPausedOrigZero :
    getOrigStorVal sentinelGatewayPauseWorldSevm pauseWorldCallee
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  change (sentinelGatewayPauseWorldState.get pauseWorldCallee).stor.get
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0
  rw [sentinelGatewayPauseWorldState_get_target]
  rfl

private theorem sentinelGatewayPauseWorld_targetPausedCold :
    (pauseWorldCallee, LidoTriggerableWithdrawalsGateway.resumeSinceSlot) ∉
      sentinelGatewayPauseWorldPre.accessedStorageKeys := by
  rw [show sentinelGatewayPauseWorldPre.accessedStorageKeys =
      Std.HashSet.emptyWithCapacity from rfl]
  exact Std.HashSet.not_mem_emptyWithCapacity

private theorem gatewayRunAfterSetBase_code :
    gatewayRunAfterSetBase.getCode pauseWorldCallee.toB256.toAdr =
      (gatewayCode controlDeployParams) := by
  have hcode := gatewayRunCode_B7
  simpa only [gatewayRunAfterSetBase, gatewayRunRemoveBase3, gatewayRunCountPost,
    gatewayRunKernelBase] using hcode

private theorem gatewayRunAfterSetBase_targetKeyCold (key : B256) :
    (pauseWorldCallee.toB256.toAdr, key) ∉
      gatewayRunAfterSetBase.accessedStorageKeys := by
  have hcallee : pauseWorldCallee.toB256.toAdr = pauseWorldCallee := by decide
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
    rw [← hcallee]
    exact h.symm


private theorem gatewayRunAfterSetBase_targetStor (key : B256) :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr key =
      controlGatewayStor.get key := by
  have haddr : pauseWorldCallee.toB256.toAdr ≠
      sentinelGatewayPauseWorldSevm.currentTarget := sentinelGatewayPauseWorld_target_ne_owner
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
  change (sentinelGatewayPauseWorldState.get pauseWorldCallee).stor.get key = _
  rw [sentinelGatewayPauseWorldState_get_target]

private theorem gatewayRunAfterSetBase_targetPausedZero :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  calc
    _ = controlGatewayStor.get
        LidoTriggerableWithdrawalsGateway.resumeSinceSlot :=
      gatewayRunAfterSetBase_targetStor _
    _ = 0 := rfl

private theorem gatewayRunAfterSetBase_roleIndex :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      (roleLookupIndexSlot pauseRole
        sentinelGatewayPauseWorldSevm.currentTarget.toB256) = 1 := by
  rw [gatewayRunAfterSetBase_targetStor, sentinelGatewayPauseWorld_currentTarget]
  rfl

private theorem gatewayRunAfterSetBase_role :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      (roleLookupRoleSlot pauseRole
        sentinelGatewayPauseWorldSevm.currentTarget.toB256) = pauseRole := by
  rw [gatewayRunAfterSetBase_targetStor, sentinelGatewayPauseWorld_currentTarget]
  rfl

private theorem gatewayRunAfterSetBase_account :
    gatewayRunAfterSetBase.getStorVal pauseWorldCallee.toB256.toAdr
      (roleLookupAccountSlot pauseRole
        sentinelGatewayPauseWorldSevm.currentTarget.toB256) =
      canonicalAccount sentinelGatewayPauseWorldSevm.currentTarget.toB256 := by
  rw [gatewayRunAfterSetBase_targetStor, sentinelGatewayPauseWorld_currentTarget]
  decide +kernel

private theorem gatewayRunAfterSetBase_count :
    gatewayRunAfterSetBase.getStorVal configWorldOwner
      (countSlot pauseWorldPauser) = 0 := by
  have hcount := gatewayRunStor_B6_count
  rw [gatewayRunAfterSetBase, addLog_getStorVal]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    hcount

private theorem gatewayRunAfterSetBase_interval :
    gatewayRunAfterSetBase.getStorVal configWorldOwner heartbeatIntervalSlot =
      pauseWorldInterval := by
  rw [gatewayRunAfterSetBase, addLog_getStorVal]
  have h := (gatewayRunStor_B6_other
    pauseWorld_interval_ne_assignCallee.symm
    pauseWorld_interval_ne_count.symm
    pauseWorld_interval_ne_entryOne.symm
    pauseWorld_interval_ne_indexCallee.symm
    pauseWorld_interval_ne_length.symm).trans sentinelPauseLastStor_interval
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using h

private theorem gatewayRunAfterSetBase_expiry :
    gatewayRunAfterSetBase.getStorVal configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  rw [gatewayRunAfterSetBase, addLog_getStorVal]
  have h := (gatewayRunStor_B6_other pauseWorld_assignCallee_ne_expiry
    pauseWorld_count_ne_expiry pauseWorld_entryOne_ne_expiry
    pauseWorld_indexCallee_ne_expiry pauseWorld_length_ne_expiry).trans
      sentinelPauseLastStor_expiry
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using h

private theorem gatewayRunAfterSetBase_accessedAddresses :
    gatewayRunAfterSetBase.accessedAddresses = Std.HashSet.emptyWithCapacity := by
  simpa only [gatewayRunAfterSetBase, gatewayRunRemoveBase3, gatewayRunCountPost,
    gatewayRunKernelBase] using gatewayRunAddrs_B7


private theorem gatewayRunAfterSetBase_warmCount :
    (sentinelGatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
      gatewayRunAfterSetBase.accessedStorageKeys := by
  rw [gatewayRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    gatewayRunWarm_count_rb3

private theorem gatewayRunAfterSetBase_warmExpiry :
    (sentinelGatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
      gatewayRunAfterSetBase.accessedStorageKeys := by
  rw [gatewayRunAfterSetBase, addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    gatewayRunWarm_expiry_rb3

private theorem gatewayRunAfterSetBase_roleIndexCold :
    (pauseWorldCallee.toB256.toAdr,
      roleLookupIndexSlot pauseRole
        sentinelGatewayPauseWorldSevm.currentTarget.toB256) ∉
      gatewayRunAfterSetBase.accessedStorageKeys :=
  gatewayRunAfterSetBase_targetKeyCold _

private theorem gatewayRunAfterSetBase_roleCold :
    (pauseWorldCallee.toB256.toAdr,
      roleLookupRoleSlot pauseRole
        sentinelGatewayPauseWorldSevm.currentTarget.toB256) ∉
      (addAccessedStorageKey gatewayRunAfterSetBase
        pauseWorldCallee.toB256.toAdr
        (roleLookupIndexSlot pauseRole
          sentinelGatewayPauseWorldSevm.currentTarget.toB256)).accessedStorageKeys := by
  rw [addAccessedStorageKey_accessedStorageKeys']
  simp only [Std.HashSet.mem_insert, beq_iff_eq, not_or]
  exact ⟨by decide +kernel, gatewayRunAfterSetBase_targetKeyCold _⟩

private theorem gatewayRunAfterSetBase_accountCold :
    (pauseWorldCallee.toB256.toAdr,
      roleLookupAccountSlot pauseRole
        sentinelGatewayPauseWorldSevm.currentTarget.toB256) ∉
      (addAccessedStorageKey
        (addAccessedStorageKey gatewayRunAfterSetBase
          pauseWorldCallee.toB256.toAdr
          (roleLookupIndexSlot pauseRole
            sentinelGatewayPauseWorldSevm.currentTarget.toB256))
        pauseWorldCallee.toB256.toAdr
        (roleLookupRoleSlot pauseRole
          sentinelGatewayPauseWorldSevm.currentTarget.toB256)).accessedStorageKeys := by
  rw [addAccessedStorageKey_accessedStorageKeys',
    addAccessedStorageKey_accessedStorageKeys']
  simp only [Std.HashSet.mem_insert, beq_iff_eq, not_or]
  exact ⟨by decide +kernel, by decide +kernel,
    gatewayRunAfterSetBase_targetKeyCold _⟩

private theorem gatewayRunAfterSetBase_resumeCold :
    (pauseWorldCallee.toB256.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { sentinelGatewayPauseWorldSevm with
          currentTarget := pauseWorldCallee.toB256.toAdr
          caller := sentinelGatewayPauseWorldSevm.currentTarget }
        gatewayRunAfterSetBase).accessedStorageKeys := by
  simp only [pauseRoleWarm, addAccessedStorageKey_accessedStorageKeys',
    Std.HashSet.mem_insert, beq_iff_eq, not_or]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    gatewayRunAfterSetBase_targetKeyCold _⟩

private theorem sentinelGatewayPauseWorld_afterSetGatewaySeam :
    ∃ mid : Devm,
      mid.stack = [] ∧
      mid.memory = pauseDecodedMemory gatewayRunMemoryLast pauseInfiniteSentinel ∧
      mid.gasLeft = 42343 ∧
      (∀ key : B256,
        mid.getStorVal configWorldOwner key =
          gatewayRunAfterSetBase.getStorVal configWorldOwner key) ∧
      (sentinelGatewayPauseWorldSevm.currentTarget, countSlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      (sentinelGatewayPauseWorldSevm.currentTarget, expirySlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      ∀ final : Devm,
        Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            sentinelGatewayPauseWorldSevm mid pauseSuccess final →
          Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            sentinelGatewayPauseWorldSevm
            (gatewayRunAfterSetBase.setMach
              ⟨[], gatewayRunMemoryLast, 75297⟩)
            pauseAfterSet final := by
  obtain ⟨mid, hstk, hmem, hgas, _herr, _hout, _hret, _hlogs,
      _hrefund, _hatd, _htrans, hask, _haddrs, _hpaused, hchain, hclose⟩ :=
    pauseAfterSet_gateway_toSuccess_runCompiled
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sentinelGatewayPauseWorldSevm gatewayRunAfterSetBase pauseWorldCallee.toB256
      pauseInfiniteSentinel gatewayRunMemoryLast gatewayRunImageLast 2600 42362
      (by simpa only [gatewayRunMemoryLast,
          gatewayRunMemoryLast] using sentinelRunMem_wfLast)
      (by simpa only [gatewayRunMemoryLast, gatewayRunImageLast,
        gatewayRunMemoryLast,
        gatewayRunImageLast] using
        sentinelRunMem_readsLast)
      (by simpa only [gatewayRunImageLast,
        gatewayRunImageLast] using sentinelRunMem_targetLast)
      (by simpa only [gatewayRunImageLast,
        gatewayRunImageLast] using sentinelRunMem_durLast)
      (by simpa only [gatewayRunMemoryLast,
        gatewayRunMemoryLast] using sentinelRunMem_sizeLast)
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
        sentinelGatewayPauseWorld_targetPausedOrigZero)
      gatewayRunAfterSetBase_resumeCold
      rfl
      (by decide)
      (by decide)
      (by decide)
      (by show (1024 : Nat) ≠ 0; decide)
      (by simpa only [toAdr_toB256] using
        sentinelGatewayPauseWorld_target_not_precompile)
      (by norm_num)
      (by
        simp only [gatewayPauseChildCost]
        norm_num)
  rcases hchain with ⟨st₁, st₂, hsub₁, hsub₂, hstate⟩
  have htargetOwner : pauseWorldCallee.toB256.toAdr ≠
      configWorldOwner := by
    simpa only [sentinelGatewayPauseWorld_currentTarget] using
      sentinelGatewayPauseWorld_target_ne_owner
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
          (pauseForProjection sentinelGatewayPauseWorldSevm.benvStat.time
            pauseInfiniteSentinel)).get configWorldOwner).stor =
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
  simp [gatewayPauseChildCost] at h
  simpa only [show (42362 + 29741 + 594 + 2600 : Nat) = 75297 from by
    norm_num] using h

private theorem sentinelGatewayPauseWorld_originalExpiry :
    getOrigStorVal sentinelGatewayPauseWorldSevm configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  change (sentinelGatewayPauseWorldState.get configWorldOwner).stor.get
    (expirySlot pauseWorldPauser) = pauseWorldExpiry
  rw [sentinelGatewayPauseWorldState_get_breaker]
  exact sentinelPauseLastStor_expiry

private def gatewayRunDecodedMemory : Mem :=
  pauseDecodedMemory gatewayRunMemoryLast pauseInfiniteSentinel

private def gatewayRunImage8 : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt gatewayRunImageLast 256 pauseForSelector.toBytes)
        288 pauseInfiniteSentinel.toBytes)
      256 isPausedSelector.toBytes)
    0 (1 : B256).toBytes

private def gatewayRunAfterSetNoLog : Devm :=
  indexClearPost sentinelGatewayPauseWorldSevm
    (entryClearPost sentinelGatewayPauseWorldSevm gatewayRunRemoveBase3
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0

private def gatewayRunMemory1 : Mem :=
  (pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel).write
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

private def gatewayRunImage1 : Bytes :=
  Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel)
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

private theorem sentinelGatewayPauseWorld_getOrigStorVal (key : B256) :
    getOrigStorVal sentinelGatewayPauseWorldSevm configWorldOwner key =
      sentinelPauseWorldStor.get key := by
  change (sentinelGatewayPauseWorldState.get configWorldOwner).stor.get key = _
  rw [sentinelGatewayPauseWorldState_get_breaker]

private theorem sentinelGatewayPauseWorld_successSuffix :
    ∃ successPre final : Devm,
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm successPre pauseSuccess final ∧
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm
          (gatewayRunAfterSetBase.setMach
            ⟨[], gatewayRunMemoryLast, 75297⟩)
          pauseAfterSet final ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm
          (gatewayRunAfterSetBase.setMach
            ⟨[], gatewayRunMemoryLast, 75297⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference sentinelGatewayPauseWorldSevm
        (gatewayRunAfterSetBase.setMach
          ⟨[], gatewayRunMemoryLast, 75297⟩) successPre := by
  obtain ⟨mid, hstk, hmem, hgas, hstor, hwarmCount, hwarmExpiry, hclose⟩ :=
    sentinelGatewayPauseWorld_afterSetGatewaySeam
  have hmidCount : mid.getStorVal sentinelGatewayPauseWorldSevm.currentTarget
      (countSlot pauseWorldPauser) = 0 := by
    rw [sentinelGatewayPauseWorld_currentTarget, hstor]
    exact gatewayRunAfterSetBase_count
  have hmidExpiry : mid.getStorVal sentinelGatewayPauseWorldSevm.currentTarget
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
    rw [sentinelGatewayPauseWorld_currentTarget, hstor]
    exact gatewayRunAfterSetBase_expiry
  have hW8 := pauseSuccess_zeroCount_ok_runCompiled
    ((runtime officialParams).main :: (runtime officialParams).aux)
    sentinelGatewayPauseWorldSevm mid gatewayRunDecodedMemory gatewayRunImage8
    pauseWorldCallee.toB256 pauseInfiniteSentinel pauseWorldPauser
    pauseWorldExpiry pauseWorldExpiry 100 2900 36021
    (by simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast,
      gatewayRunMemoryLast] using
      sentinelRunMem_wf8)
    (by simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast, gatewayRunImage8,
      gatewayRunImageLast, gatewayRunMemoryLast,
      gatewayRunImageLast] using sentinelRunMem_reads8)
    (by simpa only [gatewayRunImage8, gatewayRunImageLast,
      gatewayRunImageLast] using
      sentinelRunMem_target8)
    (by simpa only [gatewayRunImage8, gatewayRunImageLast,
      gatewayRunImageLast] using sentinelRunMem_dur8)
    (by
      have hs : gatewayRunDecodedMemory.size = 768 := by
        simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast] using
          sentinelRunMem_size8
      rw [hs])
    (by
      have hs : gatewayRunDecodedMemory.size = 768 := by
        simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast] using
          sentinelRunMem_size8
      rw [hs])
    sentinelGatewayPauseWorld_callerWord hmidCount
    (by
      unfold temporalSloadCost
      rw [if_pos hwarmCount]
      rfl)
    hmidExpiry
    (by
      rw [sentinelGatewayPauseWorld_currentTarget]
      exact sentinelGatewayPauseWorld_originalExpiry)
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
  rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_callerWord]
  constructor
  · rw [hstor, setMach_getStorVal]
  · rw [hstor, setMach_getStorVal]

private theorem sentinelGatewayPauseWorld_productionRun :
    ∃ successPre final : Devm,
      Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm
          (gatewayRunAfterSetBase.setMach
            ⟨[], gatewayRunMemoryLast, 75297⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference sentinelGatewayPauseWorldSevm
        (gatewayRunAfterSetBase.setMach
          ⟨[], gatewayRunMemoryLast, 75297⟩) successPre := by
  obtain ⟨successPre, final, hsuccess, hafter, hsuccessTo, hafterTo, hni⟩ :=
    sentinelGatewayPauseWorld_successSuffix
  have hfin := finishSetPauser_pauseAfterSet_runCompiled officialParams
    sentinelGatewayPauseWorldSevm gatewayRunAfterSetNoLog gatewayRunMemoryLast gatewayRunImageLast
    pauseWorldCallee.toB256 pauseWorldPauser 0 [] 75297 _ (by decide)
    (by simpa only [gatewayRunMemoryLast, gatewayRunImageLast,
      gatewayRunMemoryLast,
      gatewayRunImageLast] using
      sentinelRunMem_readsLast)
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using sentinelRunMem_targetLast)
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using sentinelRunMem_prevLast)
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using sentinelRunMem_newLast)
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using sentinelRunMem_contLast)
    (by
      have hs : gatewayRunMemoryLast.size = 768 := by
        simpa only [gatewayRunMemoryLast] using sentinelRunMem_sizeLast
      rw [hs]
      decide)
    (by
      have hs : gatewayRunMemoryLast.size = 768 := by
        simpa only [gatewayRunMemoryLast] using sentinelRunMem_sizeLast
      rw [hs])
    rfl
    (by
      simpa only [gatewayRunAfterSetNoLog, gatewayRunAfterSetBase,
        gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using hafter)
  rw [show (75297 + 1934 : Nat) = 77231 from by norm_num] at hfin
  have hrem := removeTarget_toFinish_coldEntry_runCompiled officialParams
    sentinelGatewayPauseWorldSevm gatewayRunCountPost gatewayRunMemory1 gatewayRunImage1
    pauseWorldCallee.toB256 0 1 [] (by decide)
    pauseWorldCallee.toB256 1 1
    2100 2100 2100 100 100 2900 2900 2900 77231 0
    (by simpa only [gatewayRunMemory1] using sentinelRunMem_wf1)
    (by simpa only [gatewayRunMemory1, gatewayRunImage1] using sentinelRunMem_reads1)
    (by simpa only [gatewayRunImage1] using sentinelRunMem_target1)
    pauseWorld_calleeValid
    (by decide) (by decide) 768 0 0 0
    (by simpa only [gatewayRunMemory1] using sentinelRunMem_size1)
    (by rw [gatewayRunMemory1, sentinelRunMem_size1])
    (by decide) (by decide) (by decide) (by decide)
    ((gatewayRunStor_countPost_other
      pauseWorld_entryOne_ne_assignCallee.symm
      pauseWorld_entryOne_ne_count.symm).trans sentinelPauseLastStor_entry)
    ((gatewayRunStor_countPost_other pauseWorld_assignCallee_ne_indexCallee
      pauseWorld_indexCallee_ne_count.symm).trans sentinelPauseLastStor_index)
    ((gatewayRunStor_countPost_other pauseWorld_length_ne_assignCallee.symm
      pauseWorld_length_ne_count.symm).trans sentinelPauseLastStor_length)
    ((sentinelGatewayPauseWorld_getOrigStorVal _).trans sentinelPauseLastStor_entry)
    ((sentinelGatewayPauseWorld_getOrigStorVal _).trans sentinelPauseLastStor_index)
    ((sentinelGatewayPauseWorld_getOrigStorVal _).trans sentinelPauseLastStor_length)
    gatewayRunCost_idxCold gatewayRunCost_lenCold gatewayRunCost_arrCold
    stubRunSvc_noop stubRunSvc_noop
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (by decide) (by norm_num [gCallStipend]) rfl _
    (by dsimp only; exact hfin)
  rw [show (0 + 77231 + 139 + 0 + 0 + 0 + 2100 + 2100 + 2100 + 100 +
    100 + 2900 + 2900 + 2900 : Nat) = 92570 from by norm_num] at hrem
  have hglue := afterOldPauser_removeTarget_runCompiled officialParams
    sentinelGatewayPauseWorldSevm gatewayRunCountPost gatewayRunMemory1 gatewayRunImage1 []
    92570 _ (by decide)
    (by simpa only [gatewayRunMemory1, gatewayRunImage1] using sentinelRunMem_reads1)
    (by simpa only [gatewayRunImage1] using sentinelRunMem_new1)
    (by rw [gatewayRunMemory1, sentinelRunMem_size1]; decide)
    (by rw [gatewayRunMemory1, sentinelRunMem_size1])
    hrem
  rw [show (92570 + 35 : Nat) = 92605 from by norm_num] at hglue
  have hker := setPauserKernel_found_runCompiled officialParams
    sentinelGatewayPauseWorldSevm gatewayRunKernelBase
    (pauseMemory pauseWorldCallee.toB256 pauseInfiniteSentinel)
    (pauseImage pauseWorldCallee.toB256 pauseInfiniteSentinel) _
    pauseWorldCallee.toB256 0 pauseWorldPauser 1 pauseWorldPauser 1
    2900 2900 92605 0
    (pauseMemory_spec pauseWorldCallee.toB256 pauseInfiniteSentinel).1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseInfiniteSentinel).2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseInfiniteSentinel).2.2.2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseInfiniteSentinel).2.2.2.2.2.2.1
    pauseWorld_calleeValid pauseWorld_pauserValid
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseInfiniteSentinel).2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      pauseInfiniteSentinel).2.2.2.2.1
    ((gatewayRunStor_kernelBase _).trans sentinelPauseLastStor_assignment)
    ((sentinelGatewayPauseWorld_getOrigStorVal _).trans sentinelPauseLastStor_assignment)
    (stubRunSvc_reset (by decide) (by decide))
    ((gatewayRunStor_assignPost_other pauseWorld_assignCallee_ne_count).trans
      sentinelPauseLastStor_count)
    ((sentinelGatewayPauseWorld_getOrigStorVal _).trans sentinelPauseLastStor_count)
    (stubRunSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend]) rfl
    (by
      dsimp only [gatewayRunKernelBase, gatewayRunCountPost, gatewayRunMemory1,
        gatewayRunImage1]
      rw [show (1 - 1 : B256) = 0 from by decide]
      exact hglue)
  rw [show foundSetPauserKernelPrefixGas sentinelGatewayPauseWorldSevm
      gatewayRunKernelBase pauseWorldCallee.toB256 0 pauseWorldPauser
      2900 2900 = 8122 from by
        simpa only [gatewayRunKernelBase] using gatewayRunKernelPrefixGas,
    show (0 + 92605 + 8122 : Nat) = 100727 from by norm_num] at hker
  have hcalldata := pauseCalldata_facts
    sentinelGatewayPauseWorld_publicPausePremises.calldata
  have hbody := pause_body_runCompiled officialParams sentinelGatewayPauseWorldSevm
    sentinelGatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldPauser
    pauseWorldExpiry pauseInfiniteSentinel 2100 2100 2100 100727 _
    hcalldata.1
    (by decide) rfl
    hcalldata.2
    sentinelGatewayPauseWorld_callerWord
    ((gatewayRunStor_lockPost _).trans sentinelPauseLastStor_assignment)
    gatewayRunCost_assignment
    (by
      unfold pauseExpiryBase
      rw [temporalSloadBase_getStorVal]
      exact (gatewayRunStor_lockPost _).trans sentinelPauseLastStor_expiry)
    gatewayRunCost_expiry
    (by decide)
    (by
      unfold pauseDurationBase pauseExpiryBase
      rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
      exact (gatewayRunStor_lockPost _).trans sentinelPauseLastStor_duration)
    gatewayRunCost_duration rfl hker
  rw [show (100727 + (469 + 2100 + 2100 + 2100) : Nat) = 107496 from by
    norm_num] at hbody
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  obtain ⟨hprog, _hcompile⟩ := pause_dispatch_runCompiledTo officialParams
    sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre 107496 0 _
    hcalldata.1
    sentinelGatewayPauseWorld_publicPausePremises.valueZero
    sentinelGatewayPauseWorld_publicPausePremises.selectorEq
    (by
      rw [sentinelGatewayPauseWorld_publicPausePremises.currentTarget]
      exact sentinelGatewayPauseWorld_publicPausePremises.codeAddress)
    sentinelGatewayPauseWorld_publicPausePremises.productionBytes hbodyTo
  have hentry : sentinelGatewayPauseWorldPre.setMach
      ⟨[], Mem.empty, 0 + pauseDispatchGas + 107496⟩ =
      sentinelGatewayPauseWorldPre := by
    rw [show (0 + pauseDispatchGas + 107496 : Nat) = sentinelGatewayPauseWorldGas from by
      norm_num [pauseDispatchGas, sentinelGatewayPauseWorldGas]]
    rfl
  rw [hentry] at hprog
  exact ⟨successPre, final, hprog, hsuccessTo, hafterTo, hni⟩

private def sentinelGatewayPauseWorldAfterSetEntry : Devm :=
  gatewayRunAfterSetBase.setMach ⟨[], gatewayRunMemoryLast, 75297⟩

private theorem sentinelGatewayPauseWorldAfterSetEntry_memory :
    sentinelGatewayPauseWorldAfterSetEntry.memory = gatewayRunMemoryLast := by
  rw [sentinelGatewayPauseWorldAfterSetEntry, Devm.memory_setMach]

private theorem gatewayRunMemoryLast_wf : Mem.Wf gatewayRunMemoryLast := by
  unfold gatewayRunMemoryLast
  exact sentinelRunMem_wfLast

private theorem gatewayRunMemoryLast_reads :
    Mem.Reads gatewayRunMemoryLast gatewayRunImageLast := by
  unfold gatewayRunMemoryLast gatewayRunImageLast
  exact sentinelRunMem_readsLast

private theorem gatewayRunImageLast_target :
    Bytes.toB256
      (gatewayRunImageLast.sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  unfold gatewayRunImageLast
  exact sentinelRunMem_targetLast

private theorem gatewayRunImageLast_duration :
    Bytes.toB256
      (gatewayRunImageLast.sliceD (durationWord * 32).toNat 32 0) =
      pauseInfiniteSentinel := by
  unfold gatewayRunImageLast
  exact sentinelRunMem_durLast

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
  have htarget := gatewayRunImageLast_target
  rw [← htarget, Bytes.toBytes_toB256_of_length hlen]

private theorem gatewayRunMemoryLast_durationWindow {devm : Devm}
    (hmemory : devm.memory = gatewayRunMemoryLast) :
    MemWordAt devm (durationWord * 32).toNat pauseInfiniteSentinel := by
  unfold MemWordAt
  rw [hmemory]
  refine ⟨gatewayRunMemoryLast_wf, gatewayRunImageLast,
    gatewayRunMemoryLast_reads, ?_⟩
  have hlen :
      (gatewayRunImageLast.sliceD (durationWord * 32).toNat 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rw [← gatewayRunImageLast_duration, Bytes.toBytes_toB256_of_length hlen]

private theorem sentinelGatewayPauseWorld_afterSetAt {final : Devm}
    (hafter : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldAfterSetEntry pauseAfterSet
      (.ok final)) :
    PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256
      pauseInfiniteSentinel (gatewayCode controlDeployParams) (.ok final)
      sentinelGatewayPauseWorldAfterSetEntry := by
  refine ⟨?_, ?_, ?_, ?_, hafter⟩
  · exact gatewayRunMemoryLast_targetWindow
      sentinelGatewayPauseWorldAfterSetEntry_memory
  · exact gatewayRunMemoryLast_durationWindow
      sentinelGatewayPauseWorldAfterSetEntry_memory
  · unfold CodeAt sentinelGatewayPauseWorldAfterSetEntry
    change gatewayRunAfterSetBase.getCode pauseWorldCallee.toB256.toAdr = _
    exact gatewayRunAfterSetBase_code
  · rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_callerWord]
    unfold sentinelGatewayPauseWorldAfterSetEntry
    rw [setMach_getStorVal, gatewayRunAfterSetBase_count,
      sentinelGatewayPauseWorld_getStorVal, sentinelPauseLastStor_count]
    decide

/-- A concrete production public pause with the installed pinned-target gateway.
The theorem exposes the production run, exact `pauseAfterSet` entry, actual
`pauseSuccess` subrun, explicit callback noninterference, combined hook,
committed outcome family, and the final pinned-target conclusion. -/
theorem sentinelGatewayPauseWorld_closedPublicPause :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256
          pauseInfiniteSentinel (gatewayCode controlDeployParams) (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference sentinelGatewayPauseWorldSevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm entry pauseWorldCallee
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams) pauseInfiniteSentinel (.ok final) ∧
      PublicPauseCommittedOutcomes sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          pauseWorldCallee.toB256 pauseInfiniteSentinel
          (gatewayCode controlDeployParams) (.ok final) ∧
      PublicPausePinnedTargetConclusion sentinelGatewayPauseWorldSevm
          sentinelGatewayPauseWorldPre pauseWorldCallee.toB256 pauseInfiniteSentinel
          (gatewayCode controlDeployParams) (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          LidoTriggerableWithdrawalsGateway.pausedUntil (.ok final) final := by
  obtain ⟨successPre, final, hprog, hsuccess, hafter, hni⟩ :=
    sentinelGatewayPauseWorld_productionRun
  have hafter' : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldAfterSetEntry pauseAfterSet
      (.ok final) := by
    simpa only [sentinelGatewayPauseWorldAfterSetEntry] using hafter
  have reached := sentinelGatewayPauseWorld_afterSetAt hafter'
  have hook := gatewayBoundaryExecutions_of_afterSet_ok
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (sevm := sentinelGatewayPauseWorldSevm) (entry := sentinelGatewayPauseWorldAfterSetEntry)
    (final := final) (target := pauseWorldCallee)
    (duration := pauseInfiniteSentinel)
    (by rfl) (by rfl) pauseWorld_callee_ne_owner
    sentinelGatewayPauseWorld_target_not_precompile
    (by
      unfold sentinelGatewayPauseWorldAfterSetEntry
      change gatewayRunAfterSetBase.getCode pauseWorldCallee = _
      rw [← show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
        toAdr_toB256 pauseWorldCallee]
      exact gatewayRunAfterSetBase_code)
    reached.1 reached.2.1 sentinelGatewayPauseWorld_publicPausePremises.dynamic hafter'
  have conclusion := sentinelGatewayPauseWorld_closedPremises hprog rfl
  refine ⟨sentinelGatewayPauseWorldAfterSetEntry, successPre, final, hprog, reached,
    hsuccess, ?_, hook, conclusion.1, conclusion⟩
  simpa only [sentinelGatewayPauseWorldAfterSetEntry] using hni

/-- The successful sentinel public pause stores the infinite sentinel itself,
not the modular sum of the block timestamp and the requested duration. -/
theorem sentinelGatewayPauseWorld_storesInfiniteSentinel :
    ∃ final : Devm,
      Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      final.getStorVal pauseWorldCallee
          LidoTriggerableWithdrawalsGateway.resumeSinceSlot = pauseInfiniteSentinel := by
  obtain ⟨_, _, final, hrun, _, _, _, _, _, _, hconclusion⟩ :=
    sentinelGatewayPauseWorld_closedPublicPause
  refine ⟨final, hrun, ?_⟩
  rcases hconclusion with ⟨_, _, hpinned, _⟩
  unfold PinnedTargetPauseWitness at hpinned
  rcases hpinned with
    ⟨_, _, _, child, _, _, _, _, _, _, _, _, _, _, _, _, hchild, hfinal⟩
  calc
    final.getStorVal pauseWorldCallee
          LidoTriggerableWithdrawalsGateway.resumeSinceSlot =
        LidoTriggerableWithdrawalsGateway.pausedUntil pauseWorldCallee
          (final.state.getStor pauseWorldCallee) := rfl
    _ = LidoTriggerableWithdrawalsGateway.pausedUntil pauseWorldCallee
          (child.state.getStor pauseWorldCallee) := by
        simpa only [toAdr_toB256] using hfinal
    _ = pauseForProjection sentinelGatewayPauseWorldSevm.benvStat.time
          pauseInfiniteSentinel := by
        simpa only [toAdr_toB256] using hchild
    _ = pauseInfiniteSentinel := by simp [pauseForProjection]

end LidoCircuitBreakerTwgSentinel

end Blanc.Composition
