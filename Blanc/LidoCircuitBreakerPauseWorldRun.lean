import Blanc.LidoCircuitBreakerPauseWorldRunKit

/-!
The composed **pause witness-world runs**, rows 19 and 18.

`Blanc/LidoCircuitBreakerPauseWorld.lean` supplies the two concrete
`pause(0x77)` entry worlds and the responder crossings;
`Blanc/LidoCircuitBreakerPauseWalk.lean` and
`Blanc/LidoCircuitBreakerPauseSuffixWalk.lean` carry the route's `.ok` walk
legs; `Blanc/LidoCircuitBreakerRegistrySubstrate.lean` owns the shared kernel
and removal walks; and `Blanc/LidoCircuitBreakerPauseWorldRunKit.lean` bridges
the legs the landed statements cannot serve directly (the cold-entry
`removeTarget` variants and the cold `SSTORE` sibling).  This leaf composes the
complete `.ok` `pause(0x77)` walk from message entry to `STOP` at both witness
worlds, each exhausting its gas to zero.

**Row 19** (`pauseLastWorldStor`): the pauser holds a single assignment, so the
pause retires it — the kernel decrements the count to zero and `pauseSuccess`
takes its zero arm, clearing the pauser's heartbeat expiry.  Entry gas `41656`.
Ledger:

* dispatch `108`;
* body `469` + three cold reads (assignment, expiry, duration: `2100` each);
* kernel prefix `122` + warm assignment re-read `100` + assignment reset
  `2900` + cold count read `2100` + count reset `2900`;
* `afterOldPauser` glue `35`;
* cold-entry `removeTarget` `139` + three cold array-region reads (`2100`
  each) + hole no-op `100` + moved-index no-op `100` + tail clear `2900` +
  length restore `2900` + index clear `2900`;
* `finishSetPauser` glue `1934`;
* `pauseAfterSet` `427` + cold `EXTCODESIZE` `2600`, containing the two
  responder crossings at `117` each inside the fixed charge;
* `pauseSuccess` zero arm `3322` + warm count re-read `100` + expiry reset
  `2900`.

**Row 18** (`pauseRetainedWorldStor`): a second target `0x88` keeps the
pauser's count at `2`, so the pause does not retire it — the kernel decrements
the count to `1`, `pauseSuccess` takes its checked arm and writes the fresh
expiry `pauseWorldInterval + pauseWorldTime`, and the removal is a genuine
swap-and-pop whose hole (`arrayEntrySlot 1`) and moved-index (`indexSlot
0x88`) writes are two extra cold `SSTORE`s.  Entry gas `53585`.  Ledger (only
the differences from row 19):

* kernel count reset is `2 → 1` rather than `1 → 0` (still `2900`);
* swap-pop `removeTarget` `139` + three cold array reads (`2100` each) + **two
  cold `SSTORE` surcharges** `2100` each (hole and moved index) + five resets
  `2900` (hole, moved index, tail clear, length restore, index clear);
* `pauseSuccess` checked arm `3351` + warm count re-read `100` + **cold
  interval read `2100`** + expiry reset `2900`.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## The concrete message -/

/-- The exact message gas of the row-19 pause run: dispatch `108` plus body
reserve `41548`, leaving `0`. -/
def pauseLastWorldGas : Nat := 41656

/-- The row-19 world's symbolic half. -/
def pauseLastSevm : Sevm := pauseWorldSevm pauseLastWorldStor pauseLastWorldGas

/-- The row-19 world's dynamic half at entry. -/
def pauseLastPre : Devm := pauseWorldPre pauseLastWorldStor pauseLastWorldGas

/-! ## Projection helpers

Small `rfl`-or-split lemmas for reading fields through the tower layers the
composition threads. -/

private theorem temporalSloadBase_error (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).error = base.error := by
  unfold temporalSloadBase
  split <;> rfl

private theorem temporalSloadBase_output (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).output = base.output := by
  unfold temporalSloadBase
  split <;> rfl

private theorem temporalSloadBase_transientStorage (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).transientStorage =
      base.transientStorage := by
  unfold temporalSloadBase
  split <;> rfl

private theorem temporalSloadBase_accessedAddresses (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).accessedAddresses =
      base.accessedAddresses := by
  unfold temporalSloadBase
  split <;> rfl

private theorem getTransVal_setTransVal_self (devm : Devm) (a : Adr)
    (k : B256) : (devm.setTransVal a k 0).getTransVal a k = 0 := by
  show ((devm.transientStorage.setStorVal a k 0).getD a .empty).get k = 0
  unfold Tra.setStorVal
  rw [Std.TreeMap.getD_eq_getD_getElem?, Tra.getElem?_set, if_pos rfl]
  split
  · show Stor.get .empty k = 0
    simp [Stor.get, Stor.empty]
  · show ((Option.getD (some _)) Stor.empty).get k = 0
    exact Stor.get_set_self _ _ _

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

private theorem lengthWritePost_getStorVal_other (sevm : Sevm) (base : Devm)
    (ol : B256) {a : Adr} {key : B256}
    (h : (a, key) ≠ (sevm.currentTarget, arrayLengthSlot)) :
    (lengthWritePost sevm base ol).getStorVal a key = base.getStorVal a key :=
  temporalSstorePost_other sevm base arrayLengthSlot ol a key h

private theorem keyPairNe {a₁ a₂ : Adr} {k₁ k₂ : B256} (h : k₂ ≠ k₁) :
    (a₁, k₁) ≠ (a₂, k₂) := fun hp => h (congrArg Prod.snd hp).symm

/-! ## The accessed-key set, stage by stage

The row-19 walk enters with both accessed sets empty, so each
`temporalSloadBase` layer resolves to its cold arm and the accessed-key set
grows by exactly the read key.  These shapes are what the cold cost equations
below read off; every non-membership is settled by slot separation, never by
deciding a `HashSet`. -/


private theorem temporalSloadBase_cold_keys (sevm : Sevm) (base : Devm)
    (key : B256)
    (h : (sevm.currentTarget, key) ∉ base.accessedStorageKeys) :
    (temporalSloadBase sevm base key).accessedStorageKeys =
      base.accessedStorageKeys.insert (sevm.currentTarget, key) := by
  unfold temporalSloadBase
  rw [if_neg h]
  rfl

private theorem lastKeys_expiryBase :
    (pauseExpiryBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256).accessedStorageKeys =
    Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256) := by
  unfold pauseExpiryBase temporalSloadBase
  rw [if_neg (show (pauseLastSevm.currentTarget,
      assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost pauseLastSevm pauseLastPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem lastKeys_durationBase :
    (pauseDurationBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    (Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser) := by
  have hnot : (pauseLastSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase pauseLastSevm pauseLastPre
        pauseWorldCallee.toB256).accessedStorageKeys := by
    rw [lastKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry
  unfold pauseDurationBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseExpiryBase pauseLastSevm pauseLastPre
    pauseWorldCallee.toB256).accessedStorageKeys).insert
    (pauseLastSevm.currentTarget, expirySlot pauseWorldPauser) = _
  rw [lastKeys_expiryBase]
  rfl

private theorem lastKeys_kernelBase :
    (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    ((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot) := by
  have hnot : (pauseLastSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase pauseLastSevm pauseLastPre
        pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
    rw [lastKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm
  unfold pauseKernelBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseDurationBase pauseLastSevm pauseLastPre
    pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys).insert
    (pauseLastSevm.currentTarget, pauseDurationSlot) = _
  rw [lastKeys_durationBase]
  rfl

private theorem lastWarm_assign_kernelBase :
    (pauseLastSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∈
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
  rw [lastKeys_kernelBase]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

private theorem lastKeys_assignPost :
    (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys = (((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)) := by
  show (assignmentBase pauseLastSevm (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser)
    pauseWorldCallee.toB256).accessedStorageKeys = _
  unfold assignmentBase temporalSloadBase
  rw [if_pos lastWarm_assign_kernelBase]
  exact lastKeys_kernelBase

private theorem lastKeys_countBase :
    (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys = ((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)) := by
  have hnot : (pauseLastSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys := by
    rw [lastKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count
  unfold temporalSloadBase
  rw [if_neg hnot]
  show ((assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys).insert
    (pauseLastSevm.currentTarget, countSlot pauseWorldPauser) = _
  rw [lastKeys_assignPost]
  rfl

private theorem lastKeys_removeBase1 :
    (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys = (((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)) := by
  have hnot : (pauseLastSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys := by
    show _ ∉ (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [lastKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee
  rw [temporalSloadBase_cold_keys _ _ _ hnot]
  show ((temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys).insert
    (pauseLastSevm.currentTarget, indexSlot pauseWorldCallee.toB256) = _
  rw [lastKeys_countBase]
  rfl

private theorem lastKeys_removeBase2 :
    (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
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
  have hnot : (pauseLastSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys := by
    rw [lastKeys_removeBase1]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_length_ne_indexCallee.symm
    · exact pauseWorld_length_ne_count.symm
    · exact pauseWorld_duration_ne_length
    · exact pauseWorld_length_ne_expiry.symm
    · exact pauseWorld_length_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, lastKeys_removeBase1]
  rfl

private theorem lastKeys_removeBase3 :
    (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
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
  have hnot : (pauseLastSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys := by
    rw [lastKeys_removeBase2]
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
  rw [temporalSloadBase_cold_keys _ _ _ hnot, lastKeys_removeBase2]
  rfl

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

private theorem lastCost_assignment :
    temporalSloadCost pauseLastSevm (pauseLockPost pauseLastSevm pauseLastPre)
      (assignmentSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseLastSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost pauseLastSevm pauseLastPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem lastCost_expiry :
    temporalSloadCost pauseLastSevm
      (pauseExpiryBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256)
      (expirySlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseLastSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256).accessedStorageKeys from by
    rw [lastKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry)]
  rfl

private theorem lastCost_duration :
    temporalSloadCost pauseLastSevm
      (pauseDurationBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256 pauseWorldPauser)
      pauseDurationSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseLastSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256
        pauseWorldPauser).accessedStorageKeys from by
    rw [lastKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm)]
  rfl

private theorem lastCost_assignWarm :
    temporalSloadCost pauseLastSevm (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser)
      (assignmentSlot pauseWorldCallee.toB256) = 100 := by
  unfold temporalSloadCost
  rw [if_pos lastWarm_assign_kernelBase]
  rfl

private theorem lastCost_countCold :
    temporalSloadCost pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseLastSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys from by
    rw [lastKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count)]
  rfl

private theorem lastCost_idxCold :
    temporalSloadCost pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseLastSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys from by
    show _ ∉ (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [lastKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee)]
  rfl

private theorem lastCost_lenCold :
    temporalSloadCost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseLastSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys from by
    rw [lastKeys_removeBase1]
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

private theorem lastCost_arrCold :
    temporalSloadCost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseLastSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys from by
    rw [lastKeys_removeBase2]
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

private theorem lastWarm_count_rb3 :
    (pauseLastSevm.currentTarget, countSlot pauseWorldPauser) ∈
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [lastKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))

private theorem lastWarm_expiry_rb3 :
    (pauseLastSevm.currentTarget, expirySlot pauseWorldPauser) ∈
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [lastKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (Std.HashSet.mem_insert.mpr
        (Or.inr Std.HashSet.mem_insert_self)))))))))

/-! ## Storage read through the tower, stage by stage

Each lemma peels exactly one named layer by rewrite, per the substrate's
one-layer transport discipline. -/

private theorem lastStor_lockPost (key : B256) :
    (pauseLockPost pauseLastSevm pauseLastPre).getStorVal configWorldOwner key =
      pauseLastWorldStor.get key := by
  show pauseLastPre.getStorVal configWorldOwner key = _
  exact pauseWorld_getStorVal pauseLastWorldStor pauseLastWorldGas

private theorem lastStor_kernelBase (key : B256) :
    (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact lastStor_lockPost key

private theorem lastStor_assignPost_other {key : B256}
    (h : assignmentSlot pauseWorldCallee.toB256 ≠ key) :
    (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  unfold assignmentPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe h)]
  unfold assignmentBase
  rw [temporalSloadBase_getStorVal]
  exact lastStor_kernelBase key

private theorem lastStor_assignPost_self :
    (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  unfold assignmentPost
  exact temporalSstorePost_self _ _ _ _

private theorem lastStor_countPost_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hc),
    temporalSloadBase_getStorVal]
  exact lastStor_assignPost_other ha

private theorem lastStor_countPost_assign :
    (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
    (keyPairNe pauseWorld_assignCallee_ne_count.symm),
    temporalSloadBase_getStorVal]
  exact lastStor_assignPost_self

private theorem lastStor_countPost_count :
    (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 :=
  temporalSstorePost_self _ _ _ _

private theorem lastStor_removeBase3_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact lastStor_countPost_other ha hc

private theorem lastStor_removeBase3_count :
    (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact lastStor_countPost_count

private theorem lastStor_removeBase3_assign :
    (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact lastStor_countPost_assign

/-! The five removal-walk writes, peeled from the outside of `B6`:
`indexClearPost` writes the index clear over the length restore, and
`entryClearPost` writes the tail clear over the moved-index and hole
writes. -/

private theorem lastStor_B6_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key)
    (hr : arrayEntrySlot 1 ≠ key)
    (hi : indexSlot pauseWorldCallee.toB256 ≠ key)
    (hl : arrayLengthSlot ≠ key) :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = pauseLastWorldStor.get key := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hl),
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr),
    show indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr)]
  exact lastStor_removeBase3_other ha hc

private theorem lastStor_B6_index :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (indexSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem lastStor_B6_length :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner arrayLengthSlot = 0 := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_indexCallee.symm),
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem lastStor_B6_entry :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (arrayEntrySlot 1) = 0 := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_indexCallee.symm),
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_entryOne),
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem lastStor_B6_assign :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_assignCallee),
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_assignCallee),
    show indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_assignCallee_ne_indexCallee.symm),
    show entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_assignCallee)]
  exact lastStor_removeBase3_assign

private theorem lastStor_B6_count :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_count),
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count),
    show indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count)]
  exact lastStor_removeBase3_count

/-! ## The staged memory and its image, through the walk's writes

`pauseMemory`'s five scratch words are staged by the body; the kernel saves
the old pauser at `previousPauserWord`, and the removal walk writes its three
scratch words above it.  Every write stays inside the `768`-byte image, so no
extension is ever charged. -/

private theorem lastMem_wf1 : Mem.Wf ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨hwf, -⟩
  exact hwf.write _ _

private theorem lastMem_reads1 : Mem.Reads ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨hwf, hreads, -⟩
  exact Mem.Reads.write hwf hreads _ _

private theorem lastMem_size1 : ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨-, -, hsize, -⟩
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, hsize]
    decide)]
  exact hsize

private theorem lastMem_target1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with
    ⟨-, -, -, -, -, htarget, -⟩
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact htarget

private theorem lastMem_new1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with
    ⟨-, -, -, -, -, -, hnew, -⟩
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact hnew

private theorem lastMem_wfLast : Mem.Wf (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  ((lastMem_wf1.write _ _).write _ _).write _ _

private theorem lastMem_readsLast : Mem.Reads (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  Mem.Reads.write ((lastMem_wf1.write _ _).write _ _)
    (Mem.Reads.write (lastMem_wf1.write _ _)
      (Mem.Reads.write lastMem_wf1 lastMem_reads1 _ _) _ _) _ _

private theorem lastMem_sizeIdx : (((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, lastMem_size1]
    decide)]
  exact lastMem_size1

private theorem lastMem_sizeLen : ((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, lastMem_sizeIdx]
    decide)]
  exact lastMem_sizeIdx

private theorem lastMem_sizeLast : (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, lastMem_sizeLen]
    decide)]
  exact lastMem_sizeLen

private theorem lastMem_targetLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact lastMem_target1

private theorem lastMem_newLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact lastMem_new1

private theorem lastMem_prevLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    show 32 = pauseWorldPauser.toBytes.length by rw [B256.length_toBytes],
    Bytes.sliceD_writeAt, B256.toB256_toBytes]

private theorem lastMem_contLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with
    ⟨-, -, -, -, -, -, -, -, hcont, -⟩
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
  exact hcont

private theorem lastMem_durLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (durationWord * 32).toNat 32 0) =
      pauseWorldDuration := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with
    ⟨-, -, -, -, -, -, -, -, -, hdur⟩
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
  exact hdur

/-! ## Value charges -/

private theorem lastSvc_reset {orig new : B256} (hnew : orig ≠ new)
    (hzero : ¬ orig = 0) : sstoreValueCost orig orig new = 2900 := by
  rw [sstoreValueCost, if_pos ⟨rfl, hnew⟩, if_neg hzero]
  norm_num [gasStorageUpdate, gasColdSload]

private theorem lastSvc_noop {orig cur : B256} :
    sstoreValueCost orig cur cur = 100 := by
  rw [sstoreValueCost, if_neg (by simp)]
  rfl

/-! ## The kernel prefix reserve, closed -/

private theorem lastKernelPrefixGas :
    foundSetPauserKernelPrefixGas pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
        pauseWorldCallee.toB256 pauseWorldPauser)
      pauseWorldCallee.toB256 0 pauseWorldPauser 2900 2900 = 8122 := by
  unfold foundSetPauserKernelPrefixGas
  rw [lastCost_assignWarm, lastCost_countCold]

/-! ## `B6` peels for the frame-meta fields -/

private theorem lastB6_peel_error :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).error = (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).error := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_error,
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_error,
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_error,
    show indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_error,
    show entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_error]

private theorem lastB6_peel_output :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).output = (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).output := by
  rw [show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_output,
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_output,
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_output,
    show indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_output,
    show entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_output]

private theorem lastRB3_error : (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).error = none := by
  rw [temporalSloadBase_error, temporalSloadBase_error,
    temporalSloadBase_error, temporalSstorePost_error,
    temporalSloadBase_error]
  show (assignmentPost pauseLastSevm
    (pauseKernelBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).error = none
  unfold assignmentPost
  rw [temporalSstorePost_error]
  unfold assignmentBase
  rw [temporalSloadBase_error]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_error, temporalSloadBase_error,
    temporalSloadBase_error]
  rfl

private theorem lastRB3_output : (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).output = [] := by
  rw [temporalSloadBase_output, temporalSloadBase_output,
    temporalSloadBase_output, temporalSstorePost_output,
    temporalSloadBase_output]
  show (assignmentPost pauseLastSevm
    (pauseKernelBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).output = []
  unfold assignmentPost
  rw [temporalSstorePost_output]
  unfold assignmentBase
  rw [temporalSloadBase_output]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_output, temporalSloadBase_output,
    temporalSloadBase_output]
  rfl

private theorem lastB6_logs : (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).logs = [] := by
  rw [indexClearPost_logs, entryClearPost_logs, temporalSloadBase_logs,
    temporalSloadBase_logs, temporalSloadBase_logs, temporalSstorePost_logs,
    temporalSloadBase_logs]
  show (assignmentPost pauseLastSevm
    (pauseKernelBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).logs = []
  unfold assignmentPost
  rw [temporalSstorePost_logs]
  unfold assignmentBase
  rw [temporalSloadBase_logs]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_logs, temporalSloadBase_logs, temporalSloadBase_logs]
  rfl

/-! ## Staged-memory sizes past the crossings -/

private theorem lastMem_sizeStaged1 : ((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, lastMem_sizeLast]
    decide)]
  exact lastMem_sizeLast

private theorem lastMem_sizeStaged2 : (((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseWorldDuration.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, lastMem_sizeStaged1]
    decide)]
  exact lastMem_sizeStaged1

private theorem lastMem_sizeStaged3 : ((((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseWorldDuration.toBytes).write 256 isPausedSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, lastMem_sizeStaged2]
    decide)]
  exact lastMem_sizeStaged2

private theorem lastMem_size8 :
    (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseWorldDuration).size = 768 := by
  unfold pauseDecodedMemory pauseStagedMemory
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, lastMem_sizeStaged3]
    decide)]
  exact lastMem_sizeStaged3

/-! ## Every other canonical pauser's expiry cell, separated from the walk's
writes -/

private theorem lastPayload_of_canonical {w : B256}
    (h : canonicalAddress w) : w.toNat < 2 ^ 252 := by
  unfold canonicalAddress at h
  exact lt_trans h (by norm_num)

private theorem lastExpiry_ne_of_ne {p : B256} (hc : canonicalAddress p)
    (hne : p ≠ pauseWorldPauser) :
    expirySlot pauseWorldPauser ≠ expirySlot p := by
  intro h
  exact hne (slot_injective_payload (by decide) (by decide)
    (lastPayload_of_canonical hc) h).symm

private theorem lastStor_B6_expiry_other {p : B256}
    (hc : canonicalAddress p) :
    (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (expirySlot p) =
      pauseLastWorldStor.get (expirySlot p) := by
  have hp : p.toNat < 2 ^ 252 := lastPayload_of_canonical hc
  refine lastStor_B6_other ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

/-! ## Account-set and code reads at the `pauseAfterSet` boundary -/

private theorem setStorVal_getCode (devm : Devm) (adr : Adr) (k v : B256)
    (a : Adr) : (devm.setStorVal adr k v).getCode a = devm.getCode a := by
  show ((devm.state.setStorVal adr k v).get a).code =
    ((devm.state.get a)).code
  unfold State.setStorVal
  by_cases h : adr = a
  · subst h
    rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

private theorem temporalSstorePost_getCode (sevm : Sevm) (base : Devm)
    (k v : B256) (a : Adr) :
    (temporalSstorePost sevm base k v).getCode a = base.getCode a := by
  show ((base.withRefundCounter _).setStorVal sevm.currentTarget k v).getCode
    a = base.getCode a
  rw [setStorVal_getCode]
  rfl

private theorem temporalSloadBase_getCode (sevm : Sevm) (base : Devm)
    (key : B256) (a : Adr) :
    (temporalSloadBase sevm base key).getCode a = base.getCode a := by
  unfold temporalSloadBase
  split <;> rfl


private theorem addAccessedStorageKey_getCode (devm : Devm) (a : Adr)
    (k : B256) (x : Adr) :
    (addAccessedStorageKey devm a k).getCode x = devm.getCode x := rfl

private theorem lengthWritePost_getCode (sevm : Sevm) (base : Devm) (ol : B256)
    (x : Adr) : (lengthWritePost sevm base ol).getCode x = base.getCode x :=
  temporalSstorePost_getCode sevm base arrayLengthSlot ol x

private theorem lastAddrs_B7 :
    ((indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨pauseLastSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  rw [addLog_accessedAddresses,
    show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_accessedAddresses,
    show entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
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
  show (assignmentPost pauseLastSevm
    (pauseKernelBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedAddresses = _
  unfold assignmentPost
  rw [temporalSstorePost_accessedAddresses]
  unfold assignmentBase
  rw [temporalSloadBase_accessedAddresses]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses]
  rfl

private theorem lastCode_B7 :
    ((indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨pauseLastSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = calleeCode := by
  rw [show ((indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨pauseLastSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr from rfl,
    show (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost pauseLastSevm
      (lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_getCode,
    show lengthWritePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_getCode,
    show (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost pauseLastSevm
      (indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_getCode,
    show indexWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_getCode,
    show entryWritePost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost pauseLastSevm
      (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
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
  show (assignmentPost pauseLastSevm
    (pauseKernelBase pauseLastSevm pauseLastPre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr =
    calleeCode
  unfold assignmentPost
  rw [temporalSstorePost_getCode]
  unfold assignmentBase
  rw [temporalSloadBase_getCode]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getCode, temporalSloadBase_getCode,
    temporalSloadBase_getCode]
  show pauseLastPre.state.getCode pauseWorldCallee.toB256.toAdr = calleeCode
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  exact pauseWorld_calleeCodeAt pauseLastWorldStor pauseLastWorldGas

private theorem lastMem_wf8 :
    Mem.Wf (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseWorldDuration) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact (((lastMem_wfLast.write _ _).write _ _).write _ _).write _ _

private theorem lastMem_reads8 :
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
  exact Mem.Reads.write (((lastMem_wfLast.write _ _).write _ _).write _ _)
    (Mem.Reads.write ((lastMem_wfLast.write _ _).write _ _)
      (Mem.Reads.write (lastMem_wfLast.write _ _)
        (Mem.Reads.write lastMem_wfLast lastMem_readsLast _ _) _ _) _ _) _ _

private theorem lastMem_target8 :
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
  exact lastMem_targetLast

private theorem lastMem_dur8 :
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
  exact lastMem_durLast

/-! ## The composed run -/

set_option maxRecDepth 40000 in
set_option maxHeartbeats 3200000 in
/-- The row-19 master composition: the boundary walk with its dichotomy
interface facts, and the complete message run with its settled effects. -/
private theorem pauseLastWorld_master :
    ∃ mid post : Devm,
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseLastSevm mid pauseSuccess (.ok post) ∧
      mid.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 ∧
      mid.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      Prog.RunCompiledTo pauseLastSevm pauseLastPre (runtime officialParams)
        (.ok post) ∧
      exec ⟨0, pauseLastSevm, pauseLastPre⟩ = .ok post ∧
      Nonempty (Exec 0 pauseLastSevm pauseLastPre (.ok post)) ∧
      post.gasLeft = 0 ∧
      post.error = none ∧
      post.output = [] ∧
      post.getTransVal configWorldOwner lockKey = 0 ∧
      post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) = 0 ∧
      post.getStorVal configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 ∧
      post.getStorVal configWorldOwner arrayLengthSlot = 0 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 1) = 0 ∧
      post.getStorVal configWorldOwner
        (indexSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      post.getStorVal configWorldOwner pauseDurationSlot =
        pauseWorldDuration ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ pauseWorldPauser →
        post.getStorVal configWorldOwner (expirySlot pauser) =
          pauseLastPre.getStorVal configWorldOwner (expirySlot pauser)) ∧
      post.logs =
        [⟨configWorldOwner,
            [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0],
            []⟩,
          ⟨configWorldOwner,
            [pauseTriggeredEvent, pauseWorldCallee.toB256, pauseWorldPauser],
            pauseWorldDuration.toBytes⟩,
          ⟨configWorldOwner, [heartbeatUpdatedEvent, pauseWorldPauser],
            (0 : B256).toBytes⟩] ∧
      some pauseLastSevm.code.toList = Prog.compile (runtime officialParams) := by
  -- the existential pauseAfterSet leg at the post-removal boundary
  obtain ⟨mid, hstk, hmem, hgas, herrF, houtF, hretF, hlogsF, hrefundF,
    hatdF, htransF, haskF, haaF, hchain, hclose⟩ :=
    pauseAfterSet_toSuccess_runCompiled
      ((runtime officialParams).main :: (runtime officialParams).aux)
      pauseLastSevm ((indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨pauseLastSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩) pauseWorldCallee.toB256 pauseWorldDuration (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) 2600 6322
      lastMem_wfLast lastMem_readsLast lastMem_targetLast lastMem_durLast
      lastMem_sizeLast
      (by
        unfold temporalAccountAccessCost
        rw [if_neg (show ¬ pauseWorldCallee.toB256.toAdr ∈ _ from by
          rw [lastAddrs_B7]
          exact Std.HashSet.not_mem_emptyWithCapacity)]
        rfl)
      lastCode_B7
      (by
        show (1024 : Nat) ≠ 0
        decide)
      (by decide)
      (by norm_num)
  -- the boundary facts the dichotomy interface consumes
  have hmidCount : mid.getStorVal configWorldOwner
      (countSlot pauseWorldPauser) = 0 := by
    rw [seam_getStorVal hchain, addLog_getStorVal]
    exact lastStor_B6_count
  have hmidInterval : mid.getStorVal configWorldOwner heartbeatIntervalSlot =
      pauseWorldInterval := by
    rw [seam_getStorVal hchain, addLog_getStorVal]
    exact (lastStor_B6_other pauseWorld_interval_ne_assignCallee.symm
      pauseWorld_interval_ne_count.symm pauseWorld_interval_ne_entryOne.symm
      pauseWorld_interval_ne_indexCallee.symm
      pauseWorld_interval_ne_length.symm).trans pauseLastStor_interval
  have hmidExpiry : mid.getStorVal configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
    rw [seam_getStorVal hchain, addLog_getStorVal]
    exact (lastStor_B6_other pauseWorld_assignCallee_ne_expiry
      pauseWorld_count_ne_expiry pauseWorld_entryOne_ne_expiry
      pauseWorld_indexCallee_ne_expiry pauseWorld_length_ne_expiry).trans
      pauseLastStor_expiry
  have hmidWarmCount : (pauseLastSevm.currentTarget,
      countSlot pauseWorldPauser) ∈ mid.accessedStorageKeys :=
    (haskF _).mpr (by
      rw [addLog_accessedStorageKeys, indexClearPost_accessedStorageKeys,
        entryClearPost_accessedStorageKeys]
      exact lastWarm_count_rb3)
  have hmidWarmExpiry : (pauseLastSevm.currentTarget,
      expirySlot pauseWorldPauser) ∈ mid.accessedStorageKeys :=
    (haskF _).mpr (by
      rw [addLog_accessedStorageKeys, indexClearPost_accessedStorageKeys,
        entryClearPost_accessedStorageKeys]
      exact lastWarm_expiry_rb3)
  -- the zero-count pauseSuccess walk from the boundary
  have hW8 := pauseSuccess_zeroCount_ok_runCompiled
    ((runtime officialParams).main :: (runtime officialParams).aux)
    pauseLastSevm mid (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseWorldDuration) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes)
    pauseWorldCallee.toB256 pauseWorldDuration pauseWorldPauser pauseWorldExpiry pauseWorldExpiry
    100 2900 0
    lastMem_wf8 lastMem_reads8 lastMem_target8 lastMem_dur8
    lastMem_size8.ge (by rw [lastMem_size8])
    (pauseWorld_callerWord pauseLastWorldStor pauseLastWorldGas)
    hmidCount
    (by
      unfold temporalSloadCost
      rw [if_pos hmidWarmCount]
      rfl)
    hmidExpiry
    ((pauseWorld_getOrigStor pauseLastWorldStor pauseLastWorldGas).trans
      pauseLastStor_expiry)
    hmidWarmExpiry
    (lastSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend])
    rfl
  have hmid_eta : mid.setMach ⟨[], pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) pauseWorldDuration,
      0 + 3322 + 100 + 2900⟩ = mid := by
    rw [show (0 + 3322 + 100 + 2900 : Nat) = 6322 from by norm_num, ← hgas,
      ← hmem, ← hstk]
    rfl
  rw [hmid_eta] at hW8
  have hboundary := Func.RunCompiledTo.of_runCompiled hW8
  -- extend through pauseAfterSet
  have hafter := hclose _ hW8
  rw [show (6322 + 427 + 2600 : Nat) = 9349 from by norm_num] at hafter
  -- through finishSetPauser
  have hfin := finishSetPauser_pauseAfterSet_runCompiled officialParams
    pauseLastSevm (indexClearPost pauseLastSevm (entryClearPost pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSloadBase pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)) arrayLengthSlot) (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
    pauseWorldCallee.toB256 pauseWorldPauser 0 [] 9349 _ (by decide)
    lastMem_readsLast lastMem_targetLast lastMem_prevLast lastMem_newLast
    lastMem_contLast (by rw [lastMem_sizeLast]; decide)
    (by rw [lastMem_sizeLast]) rfl
    hafter
  rw [show (9349 + 1934 : Nat) = 0 + 11283 from by norm_num] at hfin
  -- through the cold-entry removal walk
  have hrem := removeTarget_toFinish_coldEntry_runCompiled officialParams
    pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0) ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
    pauseWorldCallee.toB256 0 1 [] (by decide) pauseWorldCallee.toB256 1 1
    2100 2100 2100 100 100 2900 2900 2900 11283 0
    lastMem_wf1 lastMem_reads1 lastMem_target1 pauseWorld_calleeValid
    (by decide) (by decide) 768 0 0 0 lastMem_size1
    (by rw [lastMem_size1]) (by decide)
    (by decide) (by decide) (by decide)
    ((lastStor_countPost_other pauseWorld_entryOne_ne_assignCallee.symm
      pauseWorld_entryOne_ne_count.symm).trans pauseLastStor_entry)
    ((lastStor_countPost_other pauseWorld_assignCallee_ne_indexCallee
      pauseWorld_indexCallee_ne_count.symm).trans pauseLastStor_index)
    ((lastStor_countPost_other pauseWorld_length_ne_assignCallee.symm
      pauseWorld_length_ne_count.symm).trans pauseLastStor_length)
    ((pauseWorld_getOrigStor pauseLastWorldStor pauseLastWorldGas).trans
      pauseLastStor_entry)
    ((pauseWorld_getOrigStor pauseLastWorldStor pauseLastWorldGas).trans
      pauseLastStor_index)
    ((pauseWorld_getOrigStor pauseLastWorldStor pauseLastWorldGas).trans
      pauseLastStor_length)
    lastCost_idxCold lastCost_lenCold lastCost_arrCold
    lastSvc_noop lastSvc_noop (lastSvc_reset (by decide) (by decide))
    (lastSvc_reset (by decide) (by decide))
    (lastSvc_reset (by decide) (by decide))
    (by decide) (by norm_num [gCallStipend]) rfl _
    (by
      dsimp only
      exact hfin)
  rw [show (0 + 11283 + 139 + 0 + 0 + 0 + 2100 + 2100 + 2100 + 100 + 100 +
    2900 + 2900 + 2900 : Nat) = 26622 from by norm_num] at hrem
  -- through the afterOldPauser glue
  have hglue := afterOldPauser_removeTarget_runCompiled officialParams
    pauseLastSevm (temporalSstorePost pauseLastSevm (temporalSloadBase pauseLastSevm (assignmentPost pauseLastSevm
      (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0) ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
    [] 26622 _ (by decide) lastMem_reads1 lastMem_new1
    (by rw [lastMem_size1]; decide) (by rw [lastMem_size1]) hrem
  rw [show (26622 + 35 : Nat) = 0 + 26657 from by norm_num] at hglue
  -- through the shared Registry kernel
  have hker := setPauserKernel_found_runCompiled officialParams pauseLastSevm
    (pauseKernelBase pauseLastSevm pauseLastPre
      pauseWorldCallee.toB256 pauseWorldPauser)
    (pauseMemory pauseWorldCallee.toB256 pauseWorldDuration)
    (pauseImage pauseWorldCallee.toB256 pauseWorldDuration) _
    pauseWorldCallee.toB256 0 pauseWorldPauser 1 pauseWorldPauser 1 2900 2900 26657 0
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.2.2.2.1
    pauseWorld_calleeValid pauseWorld_pauserValid
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.2.1
    ((lastStor_kernelBase _).trans pauseLastStor_assignment)
    ((pauseWorld_getOrigStor pauseLastWorldStor pauseLastWorldGas).trans
      pauseLastStor_assignment)
    (lastSvc_reset (by decide) (by decide))
    ((lastStor_assignPost_other pauseWorld_assignCallee_ne_count).trans
      pauseLastStor_count)
    ((pauseWorld_getOrigStor pauseLastWorldStor pauseLastWorldGas).trans
      pauseLastStor_count)
    (lastSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend]) rfl
    (by
      dsimp only
      rw [show (1 - 1 : B256) = 0 from by decide]
      exact hglue)
  rw [lastKernelPrefixGas,
    show (0 + 26657 + 8122 : Nat) = 34779 from by norm_num] at hker
  -- through the guarded body
  have hbody := pause_body_runCompiled officialParams pauseLastSevm
    pauseLastPre pauseWorldCallee.toB256 pauseWorldPauser pauseWorldExpiry
    pauseWorldDuration 2100 2100 2100 34779 _
    (pauseWorld_dataLength pauseLastWorldStor pauseLastWorldGas)
    (by decide) rfl
    (pauseWorld_dataWord_target pauseLastWorldStor pauseLastWorldGas)
    (pauseWorld_callerWord pauseLastWorldStor pauseLastWorldGas)
    ((lastStor_lockPost _).trans pauseLastStor_assignment)
    lastCost_assignment
    (by
      unfold pauseExpiryBase
      rw [temporalSloadBase_getStorVal]
      exact (lastStor_lockPost _).trans pauseLastStor_expiry)
    lastCost_expiry
    (by
      show pauseWorldTime < pauseWorldExpiry
      decide)
    (by
      unfold pauseDurationBase pauseExpiryBase
      rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
      exact (lastStor_lockPost _).trans pauseLastStor_duration)
    lastCost_duration rfl hker
  rw [show (34779 + (469 + 2100 + 2100 + 2100) : Nat) = 0 + 41548 from by
    norm_num] at hbody
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  -- through the dispatcher
  obtain ⟨hprog, hcompile⟩ := pause_dispatch_runCompiledTo officialParams
    pauseLastSevm pauseLastPre 41548 0 _
    (pauseWorld_dataLength pauseLastWorldStor pauseLastWorldGas)
    (pauseWorld_value pauseLastWorldStor pauseLastWorldGas)
    (pauseWorld_selector pauseLastWorldStor pauseLastWorldGas)
    (pauseWorld_codeAddress_currentTarget pauseLastWorldStor
      pauseLastWorldGas)
    (pauseWorld_codeBytes pauseLastWorldStor pauseLastWorldGas) hbodyTo
  have hentry : pauseLastPre.setMach ⟨[], Mem.empty,
      0 + pauseDispatchGas + 41548⟩ = pauseLastPre := by
    rw [show (0 + pauseDispatchGas + 41548 : Nat) = pauseLastWorldGas from by
      norm_num [pauseDispatchGas, pauseLastWorldGas]]
    rfl
  rw [hentry] at hprog
  have hexec : exec ⟨0, pauseLastSevm, pauseLastPre⟩ = .ok _ :=
    Prog.exec_of_runCompiledTo hprog hcompile
  refine ⟨mid, _, hboundary, hmidCount, hmidInterval, hprog, hexec,
    (exec_iff_exec_eq 0 pauseLastSevm pauseLastPre (.ok _)).mpr hexec,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcompile⟩
  · -- error
    rw [setTransVal_error, setMach_error, addLog_error,
      temporalSstorePost_error, temporalSloadBase_error, addLog_error, herrF,
      addLog_error, lastB6_peel_error, lastRB3_error]
  · -- output
    rw [setTransVal_output, setMach_output, addLog_output,
      temporalSstorePost_output, temporalSloadBase_output, addLog_output,
      houtF, addLog_output, lastB6_peel_output, lastRB3_output]
  · -- the reentrancy lock is clear
    exact getTransVal_setTransVal_self _ _ _
  · -- the retired pauser's expiry cell
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal]
    exact temporalSstorePost_self _ _ _ _
  · -- assignment cleared
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_assignCallee_ne_expiry.symm),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal]
    exact lastStor_B6_assign
  · -- count cleared
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_count_ne_expiry.symm),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal]
    exact lastStor_B6_count
  · -- array popped
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_length_ne_expiry.symm),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal]
    exact lastStor_B6_length
  · -- array slot cleared
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_entryOne_ne_expiry.symm),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal]
    exact lastStor_B6_entry
  · -- index cleared
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_indexCallee_ne_expiry.symm),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal]
    exact lastStor_B6_index
  · -- the configured interval is untouched
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_interval_ne_expiry.symm),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal]
    exact (lastStor_B6_other pauseWorld_interval_ne_assignCallee.symm
      pauseWorld_interval_ne_count.symm pauseWorld_interval_ne_entryOne.symm
      pauseWorld_interval_ne_indexCallee.symm
      pauseWorld_interval_ne_length.symm).trans pauseLastStor_interval
  · -- the configured duration is untouched
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_duration_ne_expiry.symm),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal]
    exact (lastStor_B6_other pauseWorld_duration_ne_assignCallee.symm
      pauseWorld_duration_ne_count.symm pauseWorld_duration_ne_entryOne.symm
      pauseWorld_duration_ne_indexCallee.symm
      pauseWorld_duration_ne_length.symm).trans pauseLastStor_duration
  · -- no other canonical pauser's expiry moves
    intro pauser hcanon hne
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe (lastExpiry_ne_of_ne hcanon hne)),
      temporalSloadBase_getStorVal, addLog_getStorVal,
      seam_getStorVal hchain, addLog_getStorVal,
      lastStor_B6_expiry_other hcanon]
    exact (pauseWorld_getStorVal pauseLastWorldStor pauseLastWorldGas).symm
  · -- the three records, in order
    rw [setTransVal_logs, setMach_logs, addLog_logs, temporalSstorePost_logs,
      temporalSloadBase_logs, addLog_logs, hlogsF, addLog_logs, lastB6_logs]
    rfl

/-! ## The public payoff -/

/-- A fully inhabited production-runtime **pause**, row 19.  The assigned
pauser calls `pause(0x77)` on a CircuitBreaker deployed at `100` whose
Registry holds exactly the entry `(0x77, 9)`, with exactly `41656` gas and
both accessed sets empty.  The compiled run happens: the walk reaches `ok`
with the gas exhausted to zero, the target is unregistered — assignment
cleared, count decremented to zero, array popped, index cleared — the retired
pauser's heartbeat expiry is cleared, no other canonical pauser's expiry
moves, the reentrancy lock is released, and the three records are emitted in
order. -/
theorem pauseLastWorld_effects :
    ∃ post : Devm,
      Prog.RunCompiledTo pauseLastSevm pauseLastPre (runtime officialParams)
        (.ok post) ∧
      exec ⟨0, pauseLastSevm, pauseLastPre⟩ = .ok post ∧
      Nonempty (Exec 0 pauseLastSevm pauseLastPre (.ok post)) ∧
      post.gasLeft = 0 ∧
      post.error = none ∧
      post.output = [] ∧
      post.getTransVal configWorldOwner lockKey = 0 ∧
      post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) = 0 ∧
      post.getStorVal configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 ∧
      post.getStorVal configWorldOwner arrayLengthSlot = 0 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 1) = 0 ∧
      post.getStorVal configWorldOwner
        (indexSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      post.getStorVal configWorldOwner pauseDurationSlot =
        pauseWorldDuration ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ pauseWorldPauser →
        post.getStorVal configWorldOwner (expirySlot pauser) =
          pauseLastPre.getStorVal configWorldOwner (expirySlot pauser)) ∧
      post.logs =
        [⟨configWorldOwner,
            [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0],
            []⟩,
          ⟨configWorldOwner,
            [pauseTriggeredEvent, pauseWorldCallee.toB256, pauseWorldPauser],
            pauseWorldDuration.toBytes⟩,
          ⟨configWorldOwner, [heartbeatUpdatedEvent, pauseWorldPauser],
            (0 : B256).toBytes⟩] ∧
      some pauseLastSevm.code.toList = Prog.compile (runtime officialParams) := by
  obtain ⟨_mid, post, _hb, _hc, _hi, hprog, hexec, hne, hgas, herr, hout,
    hlock, hexp, hassign, hcount, hlen, harr, hidx, hint, hdur, hother,
    hlogs, hcompile⟩ := pauseLastWorld_master
  exact ⟨post, hprog, hexec, hne, hgas, herr, hout, hlock, hexp, hassign,
    hcount, hlen, harr, hidx, hint, hdur, hother, hlogs, hcompile⟩

/-- The shape `attainable_of_entryRoute_frame` consumes. -/
theorem pauseLastWorld_run :
    ∃ post : Devm,
      Prog.RunCompiledTo pauseLastSevm pauseLastPre (runtime officialParams)
        (.ok post) ∧
        some pauseLastSevm.code.toList =
          Prog.compile (runtime officialParams) := by
  obtain ⟨post, hprog, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hcompile⟩ := pauseLastWorld_effects
  exact ⟨post, hprog, hcompile⟩

/-- The `pauseSuccess`-entry sub-walk, in exactly the form
`pauseSuccess_expiryWrite_dichotomy` consumes: the boundary state's walk to
`.ok`, its post-callback count and configured-interval cells, and the frame
owner.  The count is stated at the walk's own caller word, which
`pauseWorld_callerWord` equates with `pauseWorldPauser`. -/
theorem pauseLastWorld_successBoundary :
    ∃ (mid : Devm) (out : Execution),
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseLastSevm mid pauseSuccess out ∧
      mid.getStorVal configWorldOwner
        (countSlot pauseLastSevm.caller.toB256) = 0 ∧
      mid.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      pauseLastSevm.currentTarget = configWorldOwner := by
  obtain ⟨mid, post, hboundary, hcount, hinterval, _⟩ :=
    pauseLastWorld_master
  exact ⟨mid, .ok post, hboundary, hcount, hinterval, rfl⟩

/-! # Row 18: the checked-count pause with swap-and-pop removal

The second witness world (`pauseRetainedWorldStor`) records a second target
`t2 = 0x88` under the same pauser, so the pauser's count is `2` and the pause
does not retire it: the kernel decrements the count to `1`, `pauseSuccess`
takes its checked arm and writes a fresh expiry `pauseWorldInterval +
pauseWorldTime`, and the removal is a genuine swap-and-pop — `0x88` moves into
`0x77`'s array slot, so the hole `arrayEntrySlot 1` and the moved target's
`indexSlot` are two cold `SSTORE`s that world-19 never pays.  Gas total
`53585`, exhausted to zero.  This section reuses the row-19 projection, cost
and value-charge helpers above; only the world-pinned facts are re-derived. -/

/-- The exact message gas of the row-18 pause run: dispatch `108` plus body
reserve `53477`, leaving `0`. -/
def pauseRetainedWorldGas : Nat := 53585

def pauseRetainedSevm : Sevm :=
  pauseWorldSevm pauseRetainedWorldStor pauseRetainedWorldGas

def pauseRetainedPre : Devm :=
  pauseWorldPre pauseRetainedWorldStor pauseRetainedWorldGas

/-! ## The accessed-key set, stage by stage (row 18) -/

private theorem retKeys_expiryBase :
    (pauseExpiryBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256).accessedStorageKeys =
    Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256) := by
  unfold pauseExpiryBase temporalSloadBase
  rw [if_neg (show (pauseRetainedSevm.currentTarget,
      assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost pauseRetainedSevm pauseRetainedPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem retKeys_durationBase :
    (pauseDurationBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    (Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser) := by
  have hnot : (pauseRetainedSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase pauseRetainedSevm pauseRetainedPre
        pauseWorldCallee.toB256).accessedStorageKeys := by
    rw [retKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry
  unfold pauseDurationBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseExpiryBase pauseRetainedSevm pauseRetainedPre
    pauseWorldCallee.toB256).accessedStorageKeys).insert
    (pauseRetainedSevm.currentTarget, expirySlot pauseWorldPauser) = _
  rw [retKeys_expiryBase]
  rfl

private theorem retKeys_kernelBase :
    (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    ((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot) := by
  have hnot : (pauseRetainedSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase pauseRetainedSevm pauseRetainedPre
        pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
    rw [retKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm
  unfold pauseKernelBase temporalSloadBase
  rw [if_neg hnot]
  show ((pauseDurationBase pauseRetainedSevm pauseRetainedPre
    pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys).insert
    (pauseRetainedSevm.currentTarget, pauseDurationSlot) = _
  rw [retKeys_durationBase]
  rfl

private theorem retWarm_assign_kernelBase :
    (pauseRetainedSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∈
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
  rw [retKeys_kernelBase]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

private theorem retKeys_assignPost :
    (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys = (((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)) := by
  show (assignmentBase pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser)
    pauseWorldCallee.toB256).accessedStorageKeys = _
  unfold assignmentBase temporalSloadBase
  rw [if_pos retWarm_assign_kernelBase]
  exact retKeys_kernelBase

private theorem retKeys_countBase :
    (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys = ((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)) := by
  have hnot : (pauseRetainedSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys := by
    rw [retKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count
  rw [temporalSloadBase_cold_keys _ _ _ hnot, retKeys_assignPost]
  rfl

private theorem retKeys_removeBase1 :
    (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys = (((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)) := by
  have hnot : (pauseRetainedSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1).accessedStorageKeys := by
    show _ ∉ (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [retKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee
  rw [temporalSloadBase_cold_keys _ _ _ hnot]
  show ((temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys).insert
    (pauseRetainedSevm.currentTarget, indexSlot pauseWorldCallee.toB256) = _
  rw [retKeys_countBase]
  rfl

private theorem retKeys_removeBase2 :
    (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys = ((((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, arrayLengthSlot)) := by
  have hnot : (pauseRetainedSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys := by
    rw [retKeys_removeBase1]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_length_ne_indexCallee.symm
    · exact pauseWorld_length_ne_count.symm
    · exact pauseWorld_duration_ne_length
    · exact pauseWorld_length_ne_expiry.symm
    · exact pauseWorld_length_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, retKeys_removeBase1]
  rfl

private theorem retKeys_removeBase3 :
    (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)).accessedStorageKeys = (((((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, arrayLengthSlot)).insert
      (configWorldOwner, arrayEntrySlot 2)) := by
  have hnot : (pauseRetainedSevm.currentTarget, arrayEntrySlot 2) ∉
      (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys := by
    rw [retKeys_removeBase2]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · exact pauseWorld_length_ne_entryTwo
    · exact pauseWorld_entryTwo_ne_indexCallee.symm
    · exact pauseWorld_entryTwo_ne_count.symm
    · exact pauseWorld_duration_ne_entryTwo
    · exact pauseWorld_entryTwo_ne_expiry.symm
    · exact pauseWorld_entryTwo_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, retKeys_removeBase2]
  rfl

/-! ## The cold and warm charges (row 18) -/

private theorem retCost_assignment :
    temporalSloadCost pauseRetainedSevm (pauseLockPost pauseRetainedSevm pauseRetainedPre)
      (assignmentSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseRetainedSevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost pauseRetainedSevm pauseRetainedPre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem retCost_expiry :
    temporalSloadCost pauseRetainedSevm
      (pauseExpiryBase pauseRetainedSevm pauseRetainedPre pauseWorldCallee.toB256)
      (expirySlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseRetainedSevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase pauseRetainedSevm pauseRetainedPre pauseWorldCallee.toB256).accessedStorageKeys from by
    rw [retKeys_expiryBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry)]
  rfl

private theorem retCost_duration :
    temporalSloadCost pauseRetainedSevm
      (pauseDurationBase pauseRetainedSevm pauseRetainedPre pauseWorldCallee.toB256 pauseWorldPauser)
      pauseDurationSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseRetainedSevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase pauseRetainedSevm pauseRetainedPre pauseWorldCallee.toB256
        pauseWorldPauser).accessedStorageKeys from by
    rw [retKeys_durationBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm)]
  rfl

private theorem retCost_assignWarm :
    temporalSloadCost pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser)
      (assignmentSlot pauseWorldCallee.toB256) = 100 := by
  unfold temporalSloadCost
  rw [if_pos retWarm_assign_kernelBase]
  rfl

private theorem retCost_countCold :
    temporalSloadCost pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseRetainedSevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys from by
    rw [retKeys_assignPost]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count)]
  rfl

private theorem retCost_idxCold :
    temporalSloadCost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseRetainedSevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1).accessedStorageKeys from by
    show _ ∉ (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
    rw [retKeys_countBase]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee)]
  rfl

private theorem retCost_lenCold :
    temporalSloadCost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseRetainedSevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys from by
    rw [retKeys_removeBase1]
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

private theorem retCost_tailCold :
    temporalSloadCost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2) = 2100 := by
  unfold temporalSloadCost
  rw [if_neg (show (pauseRetainedSevm.currentTarget, arrayEntrySlot 2) ∉
      (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys from by
    rw [retKeys_removeBase2]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · exact pauseWorld_length_ne_entryTwo
    · exact pauseWorld_entryTwo_ne_indexCallee.symm
    · exact pauseWorld_entryTwo_ne_count.symm
    · exact pauseWorld_duration_ne_entryTwo
    · exact pauseWorld_entryTwo_ne_expiry.symm
    · exact pauseWorld_entryTwo_ne_assignCallee.symm)]
  rfl

/-- The hole `arrayEntrySlot 1` is cold at the removal base: it is not among
the read keys warmed by the walk, and separates from all of them. -/
private theorem retCold_hole :
    (pauseRetainedSevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1).accessedStorageKeys := by
  show _ ∉ (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
  rw [retKeys_countBase]
  simp only [Std.HashSet.mem_insert,
    Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
    Prod.mk.injEq, not_and]
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;> decide

private theorem retCold_moved :
    (pauseRetainedSevm.currentTarget, indexSlot pauseWorldT2) ∉
      (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1).accessedStorageKeys := by
  show _ ∉ (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys
  rw [retKeys_countBase]
  simp only [Std.HashSet.mem_insert,
    Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
    Prod.mk.injEq, not_and]
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;> decide

private theorem retStor_lockPost (key : B256) :
    (pauseLockPost pauseRetainedSevm pauseRetainedPre).getStorVal configWorldOwner key =
      pauseRetainedWorldStor.get key :=
  pauseWorld_getStorVal pauseRetainedWorldStor pauseRetainedWorldGas

private theorem retStor_kernelBase (key : B256) :
    (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser).getStorVal configWorldOwner key = pauseRetainedWorldStor.get key := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact retStor_lockPost key

private theorem retStor_assignPost_other {key : B256}
    (h : assignmentSlot pauseWorldCallee.toB256 ≠ key) :
    (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = pauseRetainedWorldStor.get key := by
  unfold assignmentPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe h)]
  unfold assignmentBase
  rw [temporalSloadBase_getStorVal]
  exact retStor_kernelBase key

private theorem retStor_assignPost_self :
    (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  unfold assignmentPost
  exact temporalSstorePost_self _ _ _ _

private theorem retStor_countPost_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1).getStorVal configWorldOwner key = pauseRetainedWorldStor.get key := by
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hc),
    temporalSloadBase_getStorVal]
  exact retStor_assignPost_other ha

private theorem retStor_countPost_assign :
    (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
    (keyPairNe pauseWorld_assignCallee_ne_count.symm),
    temporalSloadBase_getStorVal]
  exact retStor_assignPost_self

private theorem retStor_countPost_count :
    (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 1 :=
  temporalSstorePost_self _ _ _ _

private theorem retStor_removeBase3_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)).getStorVal configWorldOwner key = pauseRetainedWorldStor.get key := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact retStor_countPost_other ha hc

private theorem retStor_removeBase3_count :
    (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 1 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact retStor_countPost_count

private theorem retStor_removeBase3_assign :
    (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact retStor_countPost_assign

/-! The five removal-walk writes, peeled from the outside of `RB6`. -/

private theorem retStor_RB6_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key)
    (hi : indexSlot pauseWorldCallee.toB256 ≠ key)
    (hl : arrayLengthSlot ≠ key)
    (htl : arrayEntrySlot 2 ≠ key)
    (hm : indexSlot pauseWorldT2 ≠ key)
    (hh : arrayEntrySlot 1 ≠ key) :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner key = pauseRetainedWorldStor.get key := by
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0)
      arrayLengthSlot 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hl),
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe htl),
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hm),
    addAccessedStorageKey_getStorVal,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hh),
    addAccessedStorageKey_getStorVal]
  exact retStor_removeBase3_other ha hc

private theorem retStor_RB6_index :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (indexSlot pauseWorldCallee.toB256) = 0 :=
  temporalSstorePost_self _ _ _ _

private theorem retStor_RB6_length :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner arrayLengthSlot = 1 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0)
      arrayLengthSlot 1 from rfl]
  exact temporalSstorePost_self _ _ _ _

private theorem retStor_RB6_tail :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (arrayEntrySlot 2) = 0 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0)
      arrayLengthSlot 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide))]
  exact temporalSstorePost_self _ _ _ _

private theorem retStor_RB6_moved :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (indexSlot pauseWorldT2) = 1 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0)
      arrayLengthSlot 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide))]
  exact temporalSstorePost_self _ _ _ _

private theorem retStor_RB6_hole :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (arrayEntrySlot 1) = pauseWorldT2 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0)
      arrayLengthSlot 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    addAccessedStorageKey_getStorVal]
  exact temporalSstorePost_self _ _ _ _

private theorem retStor_RB6_count :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 1 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0)
      arrayLengthSlot 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    addAccessedStorageKey_getStorVal,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    addAccessedStorageKey_getStorVal]
  exact retStor_removeBase3_count

private theorem retStor_RB6_assign :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (assignmentSlot pauseWorldCallee.toB256) = 0 := by
  rw [temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0)
      arrayLengthSlot 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    addAccessedStorageKey_getStorVal,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe (by decide)),
    addAccessedStorageKey_getStorVal]
  exact retStor_removeBase3_assign

/-! ## The staged memory and its image (row 18)

`M1` adds the saved old pauser at `previousPauserWord`; the swap-pop writes
the removed index `1`, the length `2` and the moved target `0x88` above it. -/

private theorem retMem_wf1 : Mem.Wf ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨hwf, -⟩
  exact hwf.write _ _

private theorem retMem_reads1 : Mem.Reads ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨hwf, hreads, -⟩
  exact Mem.Reads.write hwf hreads _ _

private theorem retMem_size1 : ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨-, -, hsize, -⟩
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsize]; decide)]
  exact hsize

private theorem retMem_target1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (targetWord * 32).toNat 32 0) = pauseWorldCallee.toB256 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨-, -, -, -, -, htarget, -⟩
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact htarget

private theorem retMem_new1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨-, -, -, -, -, -, hnew, -⟩
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact hnew

private theorem retMem_wfLast : Mem.Wf (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) :=
  ((retMem_wf1.write _ _).write _ _).write _ _

private theorem retMem_readsLast : Mem.Reads (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) :=
  Mem.Reads.write ((retMem_wf1.write _ _).write _ _)
    (Mem.Reads.write (retMem_wf1.write _ _)
      (Mem.Reads.write retMem_wf1 retMem_reads1 _ _) _ _) _ _

private theorem retMem_sizeIdx : (((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, retMem_size1]; decide)]
  exact retMem_size1

private theorem retMem_sizeLen : ((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, retMem_sizeIdx]; decide)]
  exact retMem_sizeIdx

private theorem retMem_sizeLast : (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, retMem_sizeLen]; decide)]
  exact retMem_sizeLen

private theorem retMem_targetLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).sliceD (targetWord * 32).toNat 32 0) = pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact retMem_target1

private theorem retMem_newLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact retMem_new1

private theorem retMem_prevLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    show 32 = pauseWorldPauser.toBytes.length by rw [B256.length_toBytes],
    Bytes.sliceD_writeAt, B256.toB256_toBytes]

private theorem retMem_contLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨-, -, -, -, -, -, -, -, hcont, -⟩
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide)]
  exact hcont

private theorem retMem_durLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).sliceD (durationWord * 32).toNat 32 0) = pauseWorldDuration := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration with ⟨-, -, -, -, -, -, -, -, -, hdur⟩
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide)]
  exact hdur

/-! ## Account, code and meta reads at the row-18 boundary

Each field is peeled one named layer at a time down to the entry world,
mirroring the row-19 discipline: `temporalSstorePost`/`lengthWritePost`/
`addAccessedStorageKey`/`temporalSloadBase` each preserve the field, so a `rw`
chain never crosses a layer by defeq. -/

private theorem retAddrs_RB6_peel :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  rw [temporalSstorePost_accessedAddresses, lengthWritePost_accessedAddresses,
    temporalSstorePost_accessedAddresses, temporalSstorePost_accessedAddresses,
    addAccessedStorageKey_accessedAddresses,
    temporalSstorePost_accessedAddresses,
    addAccessedStorageKey_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSstorePost_accessedAddresses,
    temporalSloadBase_accessedAddresses]
  show (assignmentPost pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedAddresses = _
  unfold assignmentPost
  rw [temporalSstorePost_accessedAddresses]
  unfold assignmentBase
  rw [temporalSloadBase_accessedAddresses]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses]
  rfl

private theorem retAddrs_RB7 :
    ((temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).addLog
      ⟨pauseRetainedSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  rw [addLog_accessedAddresses]
  exact retAddrs_RB6_peel

private theorem retCode_RB6_peel :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getCode pauseWorldCallee.toB256.toAdr = calleeCode := by
  rw [temporalSstorePost_getCode, lengthWritePost_getCode,
    temporalSstorePost_getCode, temporalSstorePost_getCode,
    addAccessedStorageKey_getCode, temporalSstorePost_getCode,
    addAccessedStorageKey_getCode, temporalSloadBase_getCode,
    temporalSloadBase_getCode, temporalSloadBase_getCode,
    temporalSstorePost_getCode, temporalSloadBase_getCode]
  show (assignmentPost pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getCode pauseWorldCallee.toB256.toAdr = calleeCode
  unfold assignmentPost
  rw [temporalSstorePost_getCode]
  unfold assignmentBase
  rw [temporalSloadBase_getCode]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getCode, temporalSloadBase_getCode,
    temporalSloadBase_getCode]
  show pauseRetainedPre.state.getCode pauseWorldCallee.toB256.toAdr = calleeCode
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  exact pauseWorld_calleeCodeAt pauseRetainedWorldStor pauseRetainedWorldGas

private theorem retCode_RB7 :
    ((temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).addLog
      ⟨pauseRetainedSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = calleeCode := by
  rw [addLog_getCode]
  exact retCode_RB6_peel

private theorem retRB6_error : (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).error = none := by
  rw [temporalSstorePost_error, lengthWritePost_error,
    temporalSstorePost_error, temporalSstorePost_error,
    addAccessedStorageKey_error, temporalSstorePost_error,
    addAccessedStorageKey_error, temporalSloadBase_error,
    temporalSloadBase_error, temporalSloadBase_error,
    temporalSstorePost_error, temporalSloadBase_error]
  show (assignmentPost pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).error = none
  unfold assignmentPost
  rw [temporalSstorePost_error]
  unfold assignmentBase
  rw [temporalSloadBase_error]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_error, temporalSloadBase_error,
    temporalSloadBase_error]
  rfl

private theorem retRB6_output : (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).output = [] := by
  rw [temporalSstorePost_output, lengthWritePost_output,
    temporalSstorePost_output, temporalSstorePost_output,
    addAccessedStorageKey_output, temporalSstorePost_output,
    addAccessedStorageKey_output, temporalSloadBase_output,
    temporalSloadBase_output, temporalSloadBase_output,
    temporalSstorePost_output, temporalSloadBase_output]
  show (assignmentPost pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).output = []
  unfold assignmentPost
  rw [temporalSstorePost_output]
  unfold assignmentBase
  rw [temporalSloadBase_output]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_output, temporalSloadBase_output,
    temporalSloadBase_output]
  rfl

private theorem retRB6_logs : (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).logs = [] := by
  rw [temporalSstorePost_logs, lengthWritePost_logs,
    temporalSstorePost_logs, temporalSstorePost_logs,
    addAccessedStorageKey_logs, temporalSstorePost_logs,
    addAccessedStorageKey_logs, temporalSloadBase_logs,
    temporalSloadBase_logs, temporalSloadBase_logs,
    temporalSstorePost_logs, temporalSloadBase_logs]
  show (assignmentPost pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).logs = []
  unfold assignmentPost
  rw [temporalSstorePost_logs]
  unfold assignmentBase
  rw [temporalSloadBase_logs]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_logs, temporalSloadBase_logs, temporalSloadBase_logs]
  rfl

/-! ## Warmth of count and expiry at the boundary -/

private theorem retKeys_RB6_peel :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).accessedStorageKeys =
      (((temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)).accessedStorageKeys.insert
        (pauseRetainedSevm.currentTarget, arrayEntrySlot 1)).insert
        (pauseRetainedSevm.currentTarget, indexSlot pauseWorldT2)) := by
  rw [temporalSstorePost_accessedStorageKeys,
    show (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1) = temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) arrayLengthSlot 1 from rfl,
    temporalSstorePost_accessedStorageKeys,
    temporalSstorePost_accessedStorageKeys,
    temporalSstorePost_accessedStorageKeys,
    addAccessedStorageKey_accessedStorageKeys',
    temporalSstorePost_accessedStorageKeys,
    addAccessedStorageKey_accessedStorageKeys']

private theorem retWarm_count_rb6 :
    (pauseRetainedSevm.currentTarget, countSlot pauseWorldPauser) ∈ (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).accessedStorageKeys := by
  rw [retKeys_RB6_peel, retKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (Std.HashSet.mem_insert.mpr
        (Or.inr Std.HashSet.mem_insert_self)))))))))

private theorem retWarm_expiry_rb6 :
    (pauseRetainedSevm.currentTarget, expirySlot pauseWorldPauser) ∈ (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).accessedStorageKeys := by
  rw [retKeys_RB6_peel, retKeys_removeBase3]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
        (Or.inr (Std.HashSet.mem_insert.mpr
          (Or.inr Std.HashSet.mem_insert_self)))))))))))))

/-! ## Boundary storage cells and staged memory sizes (row 18) -/

private theorem retStor_RB6_interval :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner heartbeatIntervalSlot =
      pauseWorldInterval := by
  refine (retStor_RB6_other ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans
    pauseRetainedStor_interval
  · exact pauseWorld_interval_ne_assignCallee.symm
  · exact pauseWorld_interval_ne_count.symm
  · exact pauseWorld_interval_ne_indexCallee.symm
  · exact pauseWorld_interval_ne_length.symm
  · exact pauseWorld_interval_ne_entryTwo.symm
  · exact pauseWorld_interval_ne_indexT2.symm
  · exact pauseWorld_interval_ne_entryOne.symm

private theorem retStor_RB6_expiry :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (expirySlot pauseWorldPauser) =
      pauseWorldExpiry := by
  refine (retStor_RB6_other ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans
    pauseRetainedStor_expiry
  · exact pauseWorld_assignCallee_ne_expiry
  · exact pauseWorld_count_ne_expiry
  · exact pauseWorld_indexCallee_ne_expiry
  · exact pauseWorld_length_ne_expiry
  · exact pauseWorld_entryTwo_ne_expiry
  · exact pauseWorld_indexT2_ne_expiry
  · exact pauseWorld_entryOne_ne_expiry

private theorem retStor_RB6_duration :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner pauseDurationSlot =
      pauseWorldDuration := by
  refine (retStor_RB6_other ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans
    pauseRetainedStor_duration
  · exact pauseWorld_duration_ne_assignCallee.symm
  · exact pauseWorld_duration_ne_count.symm
  · exact pauseWorld_duration_ne_indexCallee.symm
  · exact pauseWorld_duration_ne_length.symm
  · exact pauseWorld_duration_ne_entryTwo.symm
  · exact pauseWorld_duration_ne_indexT2.symm
  · exact pauseWorld_duration_ne_entryOne.symm

private theorem retPayload_of_canonical {w : B256}
    (h : canonicalAddress w) : w.toNat < 2 ^ 252 := by
  unfold canonicalAddress at h
  exact lt_trans h (by norm_num)

private theorem retExpiry_ne_of_ne {p : B256} (hc : canonicalAddress p)
    (hne : p ≠ pauseWorldPauser) : expirySlot pauseWorldPauser ≠ expirySlot p := by
  intro h
  exact hne (slot_injective_payload (by decide) (by decide)
    (retPayload_of_canonical hc) h).symm

private theorem retStor_RB6_expiry_other {p : B256}
    (hc : canonicalAddress p) :
    (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).getStorVal configWorldOwner (expirySlot p) =
      pauseRetainedWorldStor.get (expirySlot p) := by
  have hp : p.toNat < 2 ^ 252 := retPayload_of_canonical hc
  refine retStor_RB6_other ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

private theorem retMem_sizeStaged1 : ((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).write 256 pauseForSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, retMem_sizeLast]; decide)]
  exact retMem_sizeLast

private theorem retMem_sizeStaged2 : (((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseWorldDuration.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, retMem_sizeStaged1]; decide)]
  exact retMem_sizeStaged1

private theorem retMem_sizeStaged3 : ((((((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes).write 256 pauseForSelector.toBytes).write 288 pauseWorldDuration.toBytes).write 256 isPausedSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, retMem_sizeStaged2]; decide)]
  exact retMem_sizeStaged2

private theorem retMem_size8 :
    (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) pauseWorldDuration).size = 768 := by
  unfold pauseDecodedMemory pauseStagedMemory
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, retMem_sizeStaged3]; decide)]
  exact retMem_sizeStaged3

private theorem retMem_reads8 :
    Mem.Reads (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) pauseWorldDuration) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact Mem.Reads.write (((retMem_wfLast.write _ _).write _ _).write _ _)
    (Mem.Reads.write ((retMem_wfLast.write _ _).write _ _)
      (Mem.Reads.write (retMem_wfLast.write _ _)
        (Mem.Reads.write retMem_wfLast retMem_readsLast _ _) _ _) _ _) _ _

private theorem retMem_target8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes).sliceD (targetWord * 32).toNat 32 0) = pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide)]
  exact retMem_targetLast

private theorem retMem_dur8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes).sliceD (durationWord * 32).toNat 32 0) = pauseWorldDuration := by
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; decide)]
  exact retMem_durLast

/-! ## The composed row-18 run -/

private theorem retMem_wf8 :
    Mem.Wf (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) pauseWorldDuration) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact (((retMem_wfLast.write _ _).write _ _).write _ _).write _ _

private theorem ret_nof :
    B256.Nof pauseWorldTime pauseWorldInterval := by
  unfold B256.Nof pauseWorldTime pauseWorldInterval
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
private theorem pauseRetainedWorld_master :
    ∃ mid post : Devm,
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseRetainedSevm mid pauseSuccess (.ok post) ∧
      mid.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 1 ∧
      mid.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      Prog.RunCompiledTo pauseRetainedSevm pauseRetainedPre
        (runtime officialParams) (.ok post) ∧
      exec ⟨0, pauseRetainedSevm, pauseRetainedPre⟩ = .ok post ∧
      Nonempty (Exec 0 pauseRetainedSevm pauseRetainedPre (.ok post)) ∧
      post.gasLeft = 0 ∧
      post.error = none ∧
      post.output = [] ∧
      post.getTransVal configWorldOwner lockKey = 0 ∧
      post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) =
        pauseWorldInterval + pauseWorldTime ∧
      post.getStorVal configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 1 ∧
      post.getStorVal configWorldOwner arrayLengthSlot = 1 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 1) = pauseWorldT2 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 2) = 0 ∧
      post.getStorVal configWorldOwner
        (indexSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (indexSlot pauseWorldT2) = 1 ∧
      post.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      post.getStorVal configWorldOwner pauseDurationSlot =
        pauseWorldDuration ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ pauseWorldPauser →
        post.getStorVal configWorldOwner (expirySlot pauser) =
          pauseRetainedPre.getStorVal configWorldOwner (expirySlot pauser)) ∧
      post.logs =
        [⟨configWorldOwner,
            [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0],
            []⟩,
          ⟨configWorldOwner,
            [pauseTriggeredEvent, pauseWorldCallee.toB256, pauseWorldPauser],
            pauseWorldDuration.toBytes⟩,
          ⟨configWorldOwner, [heartbeatUpdatedEvent, pauseWorldPauser],
            (pauseWorldInterval + pauseWorldTime).toBytes⟩] ∧
      some pauseRetainedSevm.code.toList =
        Prog.compile (runtime officialParams) := by
  obtain ⟨mid, hstk, hmem, hgas, herrF, houtF, hretF, hlogsF, hrefundF,
    hatdF, htransF, haskF, haaF, hchain, hclose⟩ :=
    pauseAfterSet_toSuccess_runCompiled
      ((runtime officialParams).main :: (runtime officialParams).aux)
      pauseRetainedSevm ((temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0).addLog
      ⟨pauseRetainedSevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩) pauseWorldCallee.toB256 pauseWorldDuration (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) 2600 8451
      retMem_wfLast retMem_readsLast retMem_targetLast retMem_durLast
      retMem_sizeLast
      (by
        unfold temporalAccountAccessCost
        rw [if_neg (show ¬ pauseWorldCallee.toB256.toAdr ∈ _ from by
          rw [retAddrs_RB7]
          exact Std.HashSet.not_mem_emptyWithCapacity)]
        rfl)
      retCode_RB7
      (by show (1024 : Nat) ≠ 0; decide)
      (by decide)
      (by norm_num)
  have hmidCount : mid.getStorVal configWorldOwner
      (countSlot pauseWorldPauser) = 1 := by
    rw [seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_count
  have hmidInterval : mid.getStorVal configWorldOwner heartbeatIntervalSlot =
      pauseWorldInterval := by
    rw [seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_interval
  have hmidExpiry : mid.getStorVal configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
    rw [seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_expiry
  have hmidWarmExpiry : (pauseRetainedSevm.currentTarget,
      expirySlot pauseWorldPauser) ∈ mid.accessedStorageKeys :=
    (haskF _).mpr (by rw [addLog_accessedStorageKeys]; exact retWarm_expiry_rb6)
  have hmidWarmCount : (pauseRetainedSevm.currentTarget,
      countSlot pauseWorldPauser) ∈ mid.accessedStorageKeys :=
    (haskF _).mpr (by rw [addLog_accessedStorageKeys]; exact retWarm_count_rb6)
  -- the checked-count pauseSuccess walk from the boundary
  have hW8 := pauseSuccess_checkedCount_ok_runCompiled
    ((runtime officialParams).main :: (runtime officialParams).aux)
    pauseRetainedSevm mid (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) pauseWorldDuration) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes)
      256 pauseForSelector.toBytes) 288 pauseWorldDuration.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes)
    pauseWorldCallee.toB256 pauseWorldDuration pauseWorldPauser 1 pauseWorldInterval pauseWorldExpiry pauseWorldExpiry
    100 2100 2900 0
    retMem_wf8 retMem_reads8 retMem_target8 retMem_dur8
    retMem_size8.ge (by rw [retMem_size8])
    (pauseWorld_callerWord pauseRetainedWorldStor pauseRetainedWorldGas)
    hmidCount (by decide)
    (by
      unfold temporalSloadCost
      rw [if_pos hmidWarmCount]
      rfl)
    hmidInterval
    (by
      have hbase : temporalSloadBase pauseRetainedSevm mid
          (countSlot pauseWorldPauser) = mid := by
        unfold temporalSloadBase
        rw [if_pos hmidWarmCount]
      rw [hbase]
      unfold temporalSloadCost
      rw [if_neg (show (pauseRetainedSevm.currentTarget,
          heartbeatIntervalSlot) ∉ mid.accessedStorageKeys from by
        simp only [haskF, addLog_accessedStorageKeys]
        rw [retKeys_RB6_peel, retKeys_removeBase3]
        simp only [Std.HashSet.mem_insert,
          Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or,
          beq_iff_eq, Prod.mk.injEq, not_and]
        refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
          fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
          <;> decide)]
      rfl)
    (by show B256.Nof pauseWorldTime pauseWorldInterval; exact ret_nof)
    hmidExpiry
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_expiry)
    hmidWarmExpiry
    (by
      show sstoreValueCost pauseWorldExpiry pauseWorldExpiry
        (pauseWorldInterval + pauseRetainedSevm.benvStat.time) = 2900
      rw [show pauseRetainedSevm.benvStat.time = pauseWorldTime from rfl]
      exact lastSvc_reset (by decide) (by decide))
    (by
      show gCallStipend < 0 + 1496 + 2900
      norm_num [gCallStipend])
    rfl
  have hmid_eta : mid.setMach ⟨[], pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) pauseWorldDuration,
      0 + 3351 + 100 + 2100 + 2900⟩ = mid := by
    rw [show (0 + 3351 + 100 + 2100 + 2900 : Nat) = 8451 from by norm_num,
      ← hgas, ← hmem, ← hstk]
    rfl
  rw [hmid_eta] at hW8
  have hboundary := Func.RunCompiledTo.of_runCompiled hW8
  have hafter := hclose _ hW8
  rw [show (8451 + 427 + 2600 : Nat) = 11478 from by norm_num] at hafter
  have hfin := finishSetPauser_pauseAfterSet_runCompiled officialParams
    pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (lengthWritePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSstorePost pauseRetainedSevm
      (addAccessedStorageKey (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 2)) pauseRetainedSevm.currentTarget
        (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldT2) pauseRetainedSevm.currentTarget
        (indexSlot pauseWorldT2)) (indexSlot pauseWorldT2) 1)
      (arrayEntrySlot 2) 0) 1)
      (indexSlot pauseWorldCallee.toB256) 0) (((((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (2 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (2 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldT2.toBytes)
    pauseWorldCallee.toB256 pauseWorldPauser 0 [] 11478 _ (by decide)
    retMem_readsLast retMem_targetLast retMem_prevLast retMem_newLast
    retMem_contLast (by rw [retMem_sizeLast]; decide)
    (by rw [retMem_sizeLast]) rfl
    hafter
  rw [show (11478 + 1934 : Nat) = 0 + 13412 from by norm_num] at hfin
  have hrem := removeTarget_swapPop_toFinish_coldEntry_runCompiled officialParams
    pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1) ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
    pauseWorldCallee.toB256 pauseWorldT2 1 2 1 [] (by decide)
    pauseWorldCallee.toB256 2
    pauseWorldCallee.toB256 2 pauseWorldT2 2 1
    2100 2100 2100 2900 2900 2900 2900 2900 13412 0
    retMem_wf1 retMem_reads1 retMem_target1 pauseWorld_calleeValid
    pauseWorld_t2Valid.2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    768 0 0 0 retMem_size1 (by rw [retMem_size1]) (by decide)
    (by decide) (by decide) (by decide)
    ((retStor_countPost_other pauseWorld_entryOne_ne_assignCallee.symm
      pauseWorld_entryOne_ne_count.symm).trans pauseRetainedStor_entryOne)
    ((retStor_countPost_other
      (by decide : assignmentSlot pauseWorldCallee.toB256 ≠ indexSlot pauseWorldT2)
      (by decide : countSlot pauseWorldPauser ≠ indexSlot pauseWorldT2)).trans
      pauseRetainedStor_indexT2)
    ((retStor_countPost_other pauseWorld_entryTwo_ne_assignCallee.symm
      pauseWorld_entryTwo_ne_count.symm).trans pauseRetainedStor_entryTwo)
    ((retStor_countPost_other pauseWorld_assignCallee_ne_indexCallee
      pauseWorld_indexCallee_ne_count.symm).trans pauseRetainedStor_index)
    ((retStor_countPost_other pauseWorld_length_ne_assignCallee.symm
      pauseWorld_length_ne_count.symm).trans pauseRetainedStor_length)
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_entryOne)
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_indexT2)
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_entryTwo)
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_index)
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_length)
    retCost_idxCold retCost_lenCold retCost_tailCold
    retCold_hole retCold_moved
    (lastSvc_reset (by decide) (by decide))
    (lastSvc_reset (by decide) (by decide))
    (lastSvc_reset (by decide) (by decide))
    (lastSvc_reset (by decide) (by decide))
    (lastSvc_reset (by decide) (by decide))
    (by decide) (by norm_num [gCallStipend]) rfl _
    (by dsimp only; exact hfin)
  rw [show (0 + 13412 + 139 + 0 + 0 + 0 + 2100 + 2100 + 2100 + gasColdSload +
    gasColdSload + 2900 + 2900 + 2900 + 2900 + 2900 : Nat) = 38551 from by
    norm_num [gasColdSload]] at hrem
  have hglue := afterOldPauser_removeTarget_runCompiled officialParams
    pauseRetainedSevm (temporalSstorePost pauseRetainedSevm (temporalSloadBase pauseRetainedSevm (assignmentPost pauseRetainedSevm
      (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 1) ((pauseMemory pauseWorldCallee.toB256 pauseWorldDuration).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 pauseWorldDuration)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
    [] 38551 _ (by decide) retMem_reads1 retMem_new1
    (by rw [retMem_size1]; decide) (by rw [retMem_size1]) hrem
  rw [show (38551 + 35 : Nat) = 0 + 38586 from by norm_num] at hglue
  have hker := setPauserKernel_found_runCompiled officialParams pauseRetainedSevm
    (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) (pauseMemory pauseWorldCallee.toB256 pauseWorldDuration) (pauseImage pauseWorldCallee.toB256 pauseWorldDuration) _
    pauseWorldCallee.toB256 0 pauseWorldPauser 2 pauseWorldPauser 2 2900 2900 38586 0
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.2.2.2.1
    pauseWorld_calleeValid pauseWorld_pauserValid
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256 pauseWorldDuration).2.2.2.2.1
    ((retStor_kernelBase _).trans pauseRetainedStor_assignment)
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_assignment)
    (lastSvc_reset (by decide) (by decide))
    ((retStor_assignPost_other pauseWorld_assignCallee_ne_count).trans
      pauseRetainedStor_count)
    ((pauseWorld_getOrigStor pauseRetainedWorldStor pauseRetainedWorldGas).trans pauseRetainedStor_count)
    (lastSvc_reset (by decide) (by decide))
    (by norm_num [gCallStipend]) rfl
    (by
      dsimp only
      rw [show (2 - 1 : B256) = 1 from by decide]
      exact hglue)
  rw [show foundSetPauserKernelPrefixGas pauseRetainedSevm (pauseKernelBase pauseRetainedSevm pauseRetainedPre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0 pauseWorldPauser 2900 2900 =
      8122 from by
    unfold foundSetPauserKernelPrefixGas
    rw [retCost_assignWarm, retCost_countCold],
    show (0 + 38586 + 8122 : Nat) = 46708 from by norm_num] at hker
  have hbody := pause_body_runCompiled officialParams pauseRetainedSevm
    pauseRetainedPre pauseWorldCallee.toB256 pauseWorldPauser pauseWorldExpiry pauseWorldDuration 2100 2100 2100 46708 _
    (pauseWorld_dataLength pauseRetainedWorldStor pauseRetainedWorldGas) (by decide) rfl
    (pauseWorld_dataWord_target pauseRetainedWorldStor pauseRetainedWorldGas)
    (pauseWorld_callerWord pauseRetainedWorldStor pauseRetainedWorldGas)
    ((retStor_lockPost _).trans pauseRetainedStor_assignment)
    retCost_assignment
    (by
      unfold pauseExpiryBase
      rw [temporalSloadBase_getStorVal]
      exact (retStor_lockPost _).trans pauseRetainedStor_expiry)
    retCost_expiry
    (by show pauseWorldTime < pauseWorldExpiry; decide)
    (by
      unfold pauseDurationBase pauseExpiryBase
      rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
      exact (retStor_lockPost _).trans pauseRetainedStor_duration)
    retCost_duration rfl hker
  rw [show (46708 + (469 + 2100 + 2100 + 2100) : Nat) = 0 + 53477 from by
    norm_num] at hbody
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  obtain ⟨hprog, hcompile⟩ := pause_dispatch_runCompiledTo officialParams
    pauseRetainedSevm pauseRetainedPre 53477 0 _
    (pauseWorld_dataLength pauseRetainedWorldStor pauseRetainedWorldGas) (pauseWorld_value pauseRetainedWorldStor pauseRetainedWorldGas)
    (pauseWorld_selector pauseRetainedWorldStor pauseRetainedWorldGas)
    (pauseWorld_codeAddress_currentTarget pauseRetainedWorldStor pauseRetainedWorldGas)
    (pauseWorld_codeBytes pauseRetainedWorldStor pauseRetainedWorldGas) hbodyTo
  have hentry : pauseRetainedPre.setMach ⟨[], Mem.empty,
      0 + pauseDispatchGas + 53477⟩ = pauseRetainedPre := by
    rw [show (0 + pauseDispatchGas + 53477 : Nat) = pauseRetainedWorldGas from by
      norm_num [pauseDispatchGas, pauseRetainedWorldGas]]
    rfl
  rw [hentry] at hprog
  have hexec : exec ⟨0, pauseRetainedSevm, pauseRetainedPre⟩ = .ok _ :=
    Prog.exec_of_runCompiledTo hprog hcompile
  refine ⟨mid, _, hboundary, hmidCount, hmidInterval, hprog, hexec,
    (exec_iff_exec_eq 0 pauseRetainedSevm pauseRetainedPre (.ok _)).mpr hexec,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcompile⟩
  · rw [setTransVal_error, setMach_error, addLog_error,
      temporalSstorePost_error, temporalSloadBase_error,
      temporalSloadBase_error, addLog_error, herrF, addLog_error, retRB6_error]
  · rw [setTransVal_output, setMach_output, addLog_output,
      temporalSstorePost_output, temporalSloadBase_output,
      temporalSloadBase_output, addLog_output, houtF, addLog_output,
      retRB6_output]
  · exact getTransVal_setTransVal_self _ _ _
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal]
    exact temporalSstorePost_self _ _ _ _
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_assignCallee_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_assign
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_count_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_count
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_length_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_length
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_entryOne_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_hole
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_entryTwo_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_tail
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_indexCallee_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_index
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_indexT2_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_moved
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_interval_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_interval
  · rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe pauseWorld_duration_ne_expiry.symm),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal]
    exact retStor_RB6_duration
  · intro pauser hcanon hne
    rw [setTransVal_getStorVal, setMach_getStorVal, addLog_getStorVal,
      temporalSstorePost_other _ _ _ _ _ _
        (keyPairNe (retExpiry_ne_of_ne hcanon hne)),
      temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
      addLog_getStorVal, seam_getStorVal hchain, addLog_getStorVal,
      retStor_RB6_expiry_other hcanon]
    exact (pauseWorld_getStorVal pauseRetainedWorldStor pauseRetainedWorldGas).symm
  · rw [setTransVal_logs, setMach_logs, addLog_logs, temporalSstorePost_logs,
      temporalSloadBase_logs, temporalSloadBase_logs, addLog_logs, hlogsF,
      addLog_logs, retRB6_logs]
    rfl

/-! ## The public payoff (row 18) -/

/-- A fully inhabited production-runtime **pause**, row 18.  The assigned
pauser calls `pause(0x77)` on a CircuitBreaker whose Registry holds
`[(0x77, 9), (0x88, 9)]`, with exactly `53585` gas and both accessed sets
empty.  The pauser is *not* retired: the kernel decrements its count to `1`,
`pauseSuccess` takes its checked arm and writes a fresh expiry
`pauseWorldInterval + pauseWorldTime`, and the removal is a genuine
swap-and-pop — `0x88` moves into `0x77`'s array slot (a cold `SSTORE`), its
reverse index is repaired (a second cold `SSTORE`), the tail is cleared, the
length is restored to `1` and `0x77`'s index is cleared. -/
theorem pauseRetainedWorld_effects :
    ∃ post : Devm,
      Prog.RunCompiledTo pauseRetainedSevm pauseRetainedPre
        (runtime officialParams) (.ok post) ∧
      exec ⟨0, pauseRetainedSevm, pauseRetainedPre⟩ = .ok post ∧
      Nonempty (Exec 0 pauseRetainedSevm pauseRetainedPre (.ok post)) ∧
      post.gasLeft = 0 ∧
      post.error = none ∧
      post.output = [] ∧
      post.getTransVal configWorldOwner lockKey = 0 ∧
      post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) =
        pauseWorldInterval + pauseWorldTime ∧
      post.getStorVal configWorldOwner
        (assignmentSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (countSlot pauseWorldPauser) = 1 ∧
      post.getStorVal configWorldOwner arrayLengthSlot = 1 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 1) = pauseWorldT2 ∧
      post.getStorVal configWorldOwner (arrayEntrySlot 2) = 0 ∧
      post.getStorVal configWorldOwner
        (indexSlot pauseWorldCallee.toB256) = 0 ∧
      post.getStorVal configWorldOwner (indexSlot pauseWorldT2) = 1 ∧
      post.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      post.getStorVal configWorldOwner pauseDurationSlot =
        pauseWorldDuration ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ pauseWorldPauser →
        post.getStorVal configWorldOwner (expirySlot pauser) =
          pauseRetainedPre.getStorVal configWorldOwner (expirySlot pauser)) ∧
      post.logs =
        [⟨configWorldOwner,
            [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0],
            []⟩,
          ⟨configWorldOwner,
            [pauseTriggeredEvent, pauseWorldCallee.toB256, pauseWorldPauser],
            pauseWorldDuration.toBytes⟩,
          ⟨configWorldOwner, [heartbeatUpdatedEvent, pauseWorldPauser],
            (pauseWorldInterval + pauseWorldTime).toBytes⟩] ∧
      some pauseRetainedSevm.code.toList =
        Prog.compile (runtime officialParams) := by
  obtain ⟨_mid, post, _hb, _hc, _hi, hprog, hexec, hne, hgas, herr, hout,
    hlock, hexp, hassign, hcount, hlen, hh, htl, hidx, hmv, hint, hdur,
    hother, hlogs, hcompile⟩ := pauseRetainedWorld_master
  exact ⟨post, hprog, hexec, hne, hgas, herr, hout, hlock, hexp, hassign,
    hcount, hlen, hh, htl, hidx, hmv, hint, hdur, hother, hlogs, hcompile⟩

/-- The shape `attainable_of_entryRoute_frame` consumes. -/
theorem pauseRetainedWorld_run :
    ∃ post : Devm,
      Prog.RunCompiledTo pauseRetainedSevm pauseRetainedPre
        (runtime officialParams) (.ok post) ∧
        some pauseRetainedSevm.code.toList =
          Prog.compile (runtime officialParams) := by
  obtain ⟨post, hprog, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hcompile⟩ := pauseRetainedWorld_effects
  exact ⟨post, hprog, hcompile⟩

/-- The `pauseSuccess`-entry sub-walk in the form
`pauseSuccess_expiryWrite_dichotomy` consumes: the checked arm reads the
post-callback count `1` and the configured interval, and the frame owner is the
deployment. -/
theorem pauseRetainedWorld_successBoundary :
    ∃ (mid : Devm) (out : Execution),
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseRetainedSevm mid pauseSuccess out ∧
      mid.getStorVal configWorldOwner
        (countSlot pauseRetainedSevm.caller.toB256) = 1 ∧
      mid.getStorVal configWorldOwner heartbeatIntervalSlot =
        pauseWorldInterval ∧
      pauseRetainedSevm.currentTarget = configWorldOwner := by
  obtain ⟨mid, post, hboundary, hcount, hinterval, _⟩ :=
    pauseRetainedWorld_master
  exact ⟨mid, .ok post, hboundary, hcount, hinterval, rfl⟩

end Blanc.LidoCircuitBreaker
