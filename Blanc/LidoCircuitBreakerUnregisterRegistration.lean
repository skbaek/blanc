import Blanc.LidoCircuitBreakerRegistrySubstrate

/-!
Found-zero unregistration chronology for the Lido CircuitBreaker.

The target is already registered and the new pauser is zero, so `setPauser`
removes the target, taking the seven-write found-zero chronology.

The chronology splits on two independent axes, and all four combinations are
carried here from `registerAfterSet` to clean settled effects:

| old pauser | removed target's position | public boundary |
|---|---|---|
| retained (`oldCount - 1 ≠ 0`) | last (`index + 1 = entries.length`) | `registerPauser_foundZeroRetainedLast_success_settled_effects` |
| retained | interior (`index + 1 < entries.length`) | `registerPauser_foundZeroRetainedSwapPop_success_settled_effects` |
| retired (`oldCount - 1 = 0`) | last | `registerPauser_foundZeroOldLast_success_settled_effects` |
| retired | interior | `registerPauser_foundZeroOldLastSwapPop_success_settled_effects` |

The position axis selects the removal walk: the degenerate
`removeTarget_toFinish_runCompiled`, where the hole write, the moved entry's
reverse-index repair and the tail clear collapse onto one slot, or the general
`removeTarget_swapPop_toFinish_runCompiled`, where they are five distinct keys.
Both walks are chronology-independent and know nothing about `entries`; binding
the substrate's abstract `lastTarget` to the model's `sourceLastTarget entries`
out of the `RegistryWitness` is this leaf's job, and happens in the two
`setPauserKernel_*SwapPop_runCompiled` theorems.

The old-pauser axis selects the `registerAfterSet` arm: the retained arm stops
immediately, while the retired arm clears the old pauser's heartbeat expiry and
emits a zero-payload `HeartbeatUpdated(oldPauser)` after the `PauserSet` record.
The retired arm's expiry/event suffix is the substrate machinery the replacement
chronology reaches with a nonzero new pauser.

**What the settled-effects theorems pin, and what they do not.**  Each pins
`gasLeft` exactly, the emitted record list exactly (`logs = base.logs ++ [...]`,
one record in the retained rows and two in the retired rows), and every
canonical pauser's expiry cell — preserved throughout in the retained rows, and
in the retired rows `expirySlot oldPauser = 0` with every other canonical
pauser's expiry preserved.  The Registry cells the flow writes — the assignment,
the count, the two array entries, the array length and the two reverse indices —
are characterised **model-side**, by `RegistryWitness` over
`applyRegistryWrites (Devm.getStor base ca) trace.writes`, and not by an
equation between the settled state's storage and that model store.  Supplying
that operational-to-model storage equation is an open unit for this chronology.
Unlike the neighbouring replacement chronology — whose new-count bridge
`reassignedRegistryStorage_newCount` is `private` in `Registry.lean` and so out
of reach from a sibling module — the pieces this chronology would need
(`applyRegistryWrites_get`, `RegistryWitness.assignmentCountWord_pred_eq_sub_one`,
`natToB256_pred_eq_sub_one`) are all public, so the gap here is unfinished work
rather than a visibility blocker.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst


/-! ## Found-target zero-pauser registration with the old pauser retained -/

/-- The found-target/zero-pauser model branch derives the exact removal
chronology and its refined Registry witness.  The additional nonzero
post-decrement premise selects the temporal branch which preserves the old
pauser's heartbeat expiry. -/
theorem foundZeroRetainedRegistration_sourceTrace_witness
    {s : Stor} {entries : List Entry} {target oldPauser : B256}
    {index : Nat}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (_hremaining :
      Nat.toB256 (assignmentCount entries oldPauser - 1) ≠ 0) :
    ∃ trace : SetPauserSourceTrace,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      trace.writes =
        [(assignmentSlot target, 0),
         (countSlot oldPauser,
           Nat.toB256 (assignmentCount entries oldPauser - 1)),
         (arrayEntrySlot (Nat.toB256 (index + 1)),
           sourceLastTarget entries),
         (indexSlot (sourceLastTarget entries), Nat.toB256 (index + 1)),
         (arrayEntrySlot (Nat.toB256 entries.length), 0),
         (arrayLengthSlot, Nat.toB256 (entries.length - 1)),
         (indexSlot target, 0)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites s trace.writes))
        trace.postEntries := by
  have hpost : setPauser entries target 0 =
      some (swapPop entries index) := by
    simp [setPauser, htarget.1, hfind]
  have htrace : setPauserSourceTrace entries target 0 =
      some {
        postEntries := swapPop entries index
        writes :=
          [(assignmentSlot target, 0),
           (countSlot oldPauser,
             Nat.toB256 (assignmentCount entries oldPauser - 1)),
           (arrayEntrySlot (Nat.toB256 (index + 1)),
             sourceLastTarget entries),
           (indexSlot (sourceLastTarget entries), Nat.toB256 (index + 1)),
           (arrayEntrySlot (Nat.toB256 entries.length), 0),
           (arrayLengthSlot, Nat.toB256 (entries.length - 1)),
           (indexSlot target, 0)] } := by
    simp [setPauserSourceTrace, hpost,
      setPauserSourceWrites_found_zero entries target index oldPauser
        htarget.1 hfind]
  refine ⟨_, htrace, rfl, rfl, ?_⟩
  exact hw.applyFoundZeroWrites htarget hfind

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem registerAfterSet_retainedOldZero_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (oldPauser remaining : B256)
    (stack : List B256) (G : Nat)
    (hstack : stack.length ≤ 1)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (holdNonzero : oldPauser ≠ 0)
    (hremaining : remaining ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 173⟩)
      registerAfterSet (base.setMach ⟨stack, M, G⟩) := by
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewCovered :
      (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hpreviousMemory :
      (M.read (previousPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hpreviousCovered)]
  have hnewMemory :
      (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hpreviousValue :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = oldPauser := by
    rw [Mem.Reads.read hreads]
    exact hprevious
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = 0 := by
    rw [Mem.Reads.read hreads]
    exact hnew
  let oldBranch :=
    previousCountKey +++ Ninst.sload ::: Ninst.iszero :::
      ((pushB256 0 ::: loadWord previousPauserWord +++
        tagTop expiryRegion +++ Ninst.sstore ::: pushB256 0 :::
        mstoreAt 0 +++ loadWord previousPauserWord +++
        pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++
        loadWord newPauserWord +++ Ninst.iszero :::
          (Func.stop <?> (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++ loadWord newPauserWord +++
            tagTop expiryRegion +++ Ninst.sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))) <?>
       (loadWord newPauserWord +++ Ninst.iszero :::
          (Func.stop <?> (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++ loadWord newPauserWord +++
            tagTop expiryRegion +++ Ninst.sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))))
  have hcountTail : Func.RunCompiled fs sevm
      (base.setMach ⟨countSlot oldPauser :: stack, M, G + 139⟩)
      (Ninst.sload ::: Ninst.iszero :::
        ((pushB256 0 ::: loadWord previousPauserWord +++
          tagTop expiryRegion +++ Ninst.sstore ::: pushB256 0 :::
          mstoreAt 0 +++ loadWord previousPauserWord +++
          pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++
          loadWord newPauserWord +++ Ninst.iszero :::
            (Func.stop <?> (checkedHeartbeatExpiry <|
              dup 0 ::: mstoreAt 0 +++ loadWord newPauserWord +++
              tagTop expiryRegion +++ Ninst.sstore :::
              loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
              logWith 1 0 1 +++ Func.stop))) <?>
         (loadWord newPauserWord +++ Ninst.iszero :::
            (Func.stop <?> (checkedHeartbeatExpiry <|
              dup 0 ::: mstoreAt 0 +++ loadWord newPauserWord +++
              tagTop expiryRegion +++ Ninst.sstore :::
              loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
              logWith 1 0 1 +++ Func.stop)))))
      (base.setMach ⟨stack, M, G⟩) := by
    func_run (10) [0, 3, 1]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    all_goals try { simp [hnewValue, B256.eqCheck] }
    all_goals try {
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow] }
    all_goals try simp_rw [hnewMemory]
    case h_val =>
      rw [Devm.getStorVal_setMach, hcount]
      simp [B256.eqCheck, hremaining]
    case h_arm => exact Func.RunCompiled.last rfl
  have holdTail : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 151⟩) oldBranch
      (base.setMach ⟨stack, M, G⟩) := by
    exact previousCountKey_prepend_runCompiled hpreviousValue
      hpreviousMemory halign hpreviousCovered (by omega) hcountTail
  unfold registerAfterSet
  func_run (4) [3, 0]
  all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hpreviousCovered]
    norm_num [gVerylow]
  case h_val => simp [hpreviousValue, B256.eqCheck, holdNonzero]
  case h_arm =>
    rw [hpreviousMemory]
    have hg : G + 173 - 22 = G + 151 := by omega
    rw [hg]
    change Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 151⟩) oldBranch
      (base.setMach ⟨stack, M, G⟩)
    exact holdTail

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Exact `registerAfterSet` suffix for unregistering the old pauser's **last**
assignment: the previous pauser is nonzero, its remaining count is zero and the
new pauser is zero, so the walk clears the old pauser's heartbeat expiry, emits
`HeartbeatUpdated(oldPauser)` with a zero payload, and stops.  1590 gas above
the caller's reserve plus the expiry-clear value cost — 1567 for the shared
old-last prefix and 23 for the zero new-pauser load, its `iszero` and the taken
branch to `Func.stop`.

This is the old-last counterpart of `registerAfterSet_retainedOldZero_runCompiled`.
Lifting it through `finishSetPauser` and the removal walk is the next unit; the
shared prefix it composes with lives in the substrate, because the replacement
chronology reaches the same prefix with a nonzero new pauser. -/
theorem registerAfterSet_oldLastZero_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (oldPauser oldExpiry oldExpiryOriginal : B256)
    (stack : List B256) (clearCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (holdNonzero : oldPauser ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget (countSlot oldPauser) = 0)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 1590 + clearCost⟩)
      registerAfterSet
      (((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
          (0 : B256).toBytes⟩).setMach
        ⟨stack, M.write 0 (0 : B256).toBytes, G⟩) := by
  let M' := M.write 0 (0 : B256).toBytes
  let img' := Bytes.writeAt img 0 (0 : B256).toBytes
  have hsizeM' : M'.size = M.size :=
    Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show 0 + 32 ≤ M.size by omega))
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads 0 _
  have hnewCovered' : (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewMemory' : (M'.read (newPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hnewCovered')]
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      simp only [B256.length_toBytes]
      decide)]
    exact hnew
  have hnewValue' :
      (M'.read (newPauserWord * 32).toNat 32).1.toB256 = 0 := by
    rw [Mem.Reads.read hreads']
    exact hnew'
  have htail : Func.RunCompiled fs sevm
      (((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
          (0 : B256).toBytes⟩).setMach ⟨stack, M', G + 23⟩)
      (loadWord newPauserWord +++ Ninst.iszero :::
        (Func.stop <?>
          (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++
            Ninst.sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop)))
      (((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
          (0 : B256).toBytes⟩).setMach ⟨stack, M', G⟩) := by
    func_run (4) [3, 1]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign' hnewCovered']
      norm_num [gVerylow]
    case h_val => simp [hnewValue', B256.eqCheck]
    case h_arm =>
      rw [hnewMemory']
      exact Func.RunCompiled.last rfl
  have h := registerAfterSet_oldLast_newPauserTail_runCompiled fs sevm base M
    img oldPauser oldExpiry oldExpiryOriginal stack clearCost (G + 23)
    (((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
      ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
        (0 : B256).toBytes⟩).setMach ⟨stack, M', G⟩)
    hstack hwf hreads hprevious holdNonzero hcount hwarmCount hexpiry
    hexpiryOrig hwarmExpiry hclearCost (by omega) hstatic hsize halign htail
  have hg : G + 23 + 1567 + clearCost = G + 1590 + clearCost := by omega
  rw [hg] at h
  exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem finishSetPauser_retainedOldZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldPauser remaining : B256) (stack : List B256) (G : Nat)
    (hstack : stack.length ≤ 1)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (holdNonzero : oldPauser ≠ 0)
    (hremaining : remaining ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hstatic : sevm.isStatic = false) :
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G + 2108⟩) finishSetPauser
      ((base.addLog eventLog).setMach ⟨stack, M, G⟩) := by
  dsimp only
  have hregister : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux)
      sevm ((base.addLog ⟨sevm.currentTarget,
        [pauserSetEvent, target, oldPauser, 0], []⟩).setMach
        ⟨stack, M, G + 173⟩) registerAfterSet
      ((base.addLog ⟨sevm.currentTarget,
        [pauserSetEvent, target, oldPauser, 0], []⟩).setMach
        ⟨stack, M, G⟩) := by
    apply registerAfterSet_retainedOldZero_runCompiled _ sevm _
      M img oldPauser remaining stack G hstack hreads hprevious hnew
      holdNonzero hremaining
    · exact hcount
    · exact hwarmCount
    · exact hsize
    · exact halign
  have h := finishSetPauser_registerAfterSet_runCompiled dp sevm base M img
    target oldPauser 0 stack (G + 173)
    ((base.addLog ⟨sevm.currentTarget,
      [pauserSetEvent, target, oldPauser, 0], []⟩).setMach ⟨stack, M, G⟩)
    hstack hreads htarget hprevious hnew hcontinuation hsize halign
    hstatic hregister
  have hg : G + 173 + 1935 = G + 2108 := by omega
  rw [hg] at h
  exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem removeTarget_foundZeroRetained_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next oldPauser remaining : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hremaining : remaining ≠ 0)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = next)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal next next =
      movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal next 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget, arrayEntrySlot next) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : next - 1 = oldLength)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 2551 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost⟩)
      removeTarget
      (((indexClearPost sevm
          (entryClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨stack, MLast, G⟩) := by
  dsimp only
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let countKey := countSlot oldPauser
  let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    target.toBytes
  let tailPost := entryClearPost sevm base target next
  let removePost := indexClearPost sevm tailPost target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  have hwfIndex : Mem.Wf MIndex := hwf.write _ _
  have hreadsIndex : Mem.Reads MIndex imgIndex :=
    Mem.Reads.write hwf hreads _ _
  have hwfLength : Mem.Wf MLength := hwfIndex.write _ _
  have hreadsLength : Mem.Reads MLength imgLength :=
    Mem.Reads.write hwfIndex hreadsIndex _ _
  have hreadsLast : Mem.Reads MLast imgLast :=
    Mem.Reads.write hwfLength hreadsLength _ _
  have hsizeIndex : MIndex.size = max entrySize 672 := by
    dsimp only [MIndex]
    rw [Mem.size_write_word_at,
      show (removedIndexWord * 32).toNat + 32 = 672 by decide, hsize,
      show ceil32 672 = 672 by decide]
    split <;> omega
  have hsizeLength : MLength.size = 704 := by
    dsimp only [MLength]
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide,
      hsizeIndex, show ceil32 704 = 704 by decide]
    split <;> omega
  have hsizeLast : MLast.size = 736 := by
    dsimp only [MLast]
    rw [Mem.size_write_word_at,
      show (lastTargetWord * 32).toNat + 32 = 736 by decide,
      hsizeLength]
    split
    · omega
    · decide
  have halignIndex : MIndex.size % 32 = 0 :=
    Mem.aligned_write_word halign
  have halignLength : MLength.size % 32 = 0 :=
    Mem.aligned_write_word halignIndex
  have halignLast : MLast.size % 32 = 0 :=
    Mem.aligned_write_word halignLength
  have earlierLast {word : B256}
      (hindexBefore : (word * 32).toNat + 32 ≤
        (removedIndexWord * 32).toNat)
      (hlengthBefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat)
      (hlastBefore : (word * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat) :
      Bytes.toB256 (imgLast.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlastBefore]
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlengthBefore]
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hindexBefore]
  have htargetLast : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target :=
    (earlierLast (by decide) (by decide) (by decide)).trans htarget
  have hpreviousLast : Bytes.toB256
      (imgLast.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser :=
    (earlierLast (by decide) (by decide) (by decide)).trans hprevious
  have hnewLast : Bytes.toB256
      (imgLast.sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hnew
  have hcontinuationLast : Bytes.toB256
      (imgLast.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hcontinuation
  have harrayFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hnextBound
  have hpairs := registryAddressFamilies_pairwise
    htargetValid.2 htargetValid.2 holdValid.2
  have hlengthCount := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have hcountRemove : removePost.getStorVal sevm.currentTarget countKey =
      remaining := by
    simp only [removePost, tailPost, indexClearPost,
      lengthWritePost, entryClearPost,
      indexWritePost, entryWritePost]
    rw [temporalSstorePost_other _ _ (indexSlot target) 0 _ countKey
        (pairNe (Ne.symm hpairs.2.2)),
      temporalSstorePost_other _ _ arrayLengthSlot oldLength _ countKey
        (pairNe hlengthCount.2.2),
      temporalSstorePost_other _ _ arrayKey 0 _ countKey
        (pairNe harrayFamilies.2.2),
      temporalSstorePost_other _ _ indexKey next _ countKey
        (pairNe hpairs.2.2.symm),
      temporalSstorePost_other _ _ arrayKey target _ countKey
        (pairNe harrayFamilies.2.2)]
    exact hcount
  have hwarmCountRemove : (sevm.currentTarget, countKey) ∈
      removePost.accessedStorageKeys := by
    simp only [removePost, tailPost, indexClearPost,
      lengthWritePost, entryClearPost,
      indexWritePost, entryWritePost,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmCount
  have hfinish := finishSetPauser_retainedOldZero_runCompiled dp sevm
    removePost MLast imgLast target oldPauser remaining stack G hstack hreadsLast
    htargetLast hpreviousLast hnewLast hcontinuationLast holdValid.1
    hremaining (by simpa only [countKey] using hcountRemove)
    (by simpa only [countKey] using hwarmCountRemove)
    (by rw [hsizeLast]; decide) halignLast hstatic
  have hrun := removeTarget_runCompiled dp sevm base M img
    target oldLength next oldPauser stack hstack arrayOriginal indexOriginal
    lengthOriginal holeCost movedIndexCost tailClearCost lengthRestoreCost
    indexClearCost 2108 G hwf hreads htarget htargetValid hnextNonzero
    hnextBound entrySize indexExtCost lengthExtCost 4 hsize halign hentryLow
    hindexExtCost hlengthExtCost
    (by rw [Nat.max_eq_right hentryHigh]; decide)
    harray hindex hlength harrayOrig hindexOrig
    hlengthOrig hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
    hindexClearCost hwarmArray hwarmIndex hwarmLength hsub hgasFinal hstatic
    (by simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog]
      using hfinish)
  have hg : G + 2108 + 439 + 4 + indexExtCost + lengthExtCost + holeCost +
      movedIndexCost + tailClearCost +
      lengthRestoreCost + indexClearCost =
      G + 2551 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost := by omega
  rw [hg] at hrun
  simpa only [MIndex, MLength, MLast, eventLog] using hrun

private theorem afterOldPauser_foundZeroRetained_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next oldPauser remaining : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hremaining : remaining ≠ 0)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = next)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal next next =
      movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal next 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget, arrayEntrySlot next) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : next - 1 = oldLength)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 2586 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost⟩)
      afterOldPauser
      (((indexClearPost sevm
          (entryClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨stack, MLast, G⟩) := by
  dsimp only
  let fs := (runtime dp).main :: (runtime dp).aux
  let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  have hremove := removeTarget_foundZeroRetained_runCompiled dp sevm base M
    img target oldLength next oldPauser remaining stack hstack arrayOriginal
    indexOriginal lengthOriginal holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost G hwf hreads htarget hprevious hnew
    hcontinuation htargetValid holdValid hremaining hnextNonzero hnextBound
    entrySize indexExtCost lengthExtCost hsize halign hentryLow hentryHigh
    hindexExtCost hlengthExtCost
    harray hindex hlength hcount harrayOrig hindexOrig
    hlengthOrig hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
    hindexClearCost hwarmArray hwarmIndex hwarmLength hwarmCount hsub
    hgasFinal hstatic
  have h := afterOldPauser_removeTarget_runCompiled dp sevm base M img
    stack
    (G + 2551 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
      tailClearCost + lengthRestoreCost + indexClearCost)
    (((indexClearPost sevm
        (entryClearPost sevm base target next)
        target oldLength).addLog eventLog).setMach ⟨stack, MLast, G⟩)
    hstack hreads hnew (by omega) halign
    (by simpa only [fs, MIndex, MLength, MLast, eventLog] using hremove)
  have hg : G + 2551 + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost + 35 =
      G + 2586 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost := by omega
  rw [hg] at h
  exact h

/-- Exact reserve for the found-target/zero-pauser kernel restricted to
removing the array's last entry while the old pauser is retained.  It includes
the actual assignment and count SLOAD costs, the seven exact SSTORE
value-cost partitions, and the fixed removal-walk memory growth at a 640-byte
entry size. -/
private def foundZeroRetainedLastSetPauserKernelGas (sevm : Sevm) (base : Devm)
    (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost : Nat) : Nat :=
  2714 + temporalSloadCost sevm base (assignmentSlot target) + assignmentCost +
    temporalSloadCost sevm (assignmentPost sevm base target 0)
      (countSlot oldPauser) + countCost + holeCost + movedIndexCost +
    tailClearCost + lengthRestoreCost + indexClearCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-kernel success for unregistering a recorded target, under
the two restrictions the removal machinery currently supports.  First, the
removed target is **already the last array element** (`index + 1 =
entries.length`), so the swap step rewrites the hole with the target itself.
Second, the old pauser is **retained**: its decremented assignment count stays
nonzero, so `registerAfterSet` takes the else arm and, seeing a zero new
pauser, stops without touching any expiry slot.  The seven-write removal
chronology derives the `swapPop` Registry trace and witness, the lone
`PauserSet` log, and preservation of every canonical expiry slot. -/
theorem setPauserKernel_foundZeroRetainedLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (entries : List Entry) (target : B256)
    (index : Nat) (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hsize : M.size = 640)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M,
          G + foundZeroRetainedLastSetPauserKernelGas sevm base target
            oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost⟩)
        setPauserKernel post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have hindexLt : index < entries.length := findEntry_index_lt hfind
  let next : B256 := Nat.toB256 entries.length
  let oldLength : B256 := next - 1
  let assignPost := assignmentPost sevm base target 0
  let countBase := temporalSloadBase sevm assignPost (countSlot oldPauser)
  let countPost := temporalSstorePost sevm countBase (countSlot oldPauser)
    (oldCount - 1)
  let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    oldPauser.toBytes
  have hlength256 := hw.entries_length_lt_2pow256
  have hnextBound : next.toNat < 2 ^ 252 := by
    dsimp only [next]
    rw [B256.toNat_toB256_of_lt hlength256]
    exact hw.entries_length_lt_2pow252
  have hnextNonzero : next ≠ 0 := by
    intro hz
    have h := congrArg B256.toNat hz
    rw [show next = Nat.toB256 entries.length from rfl,
      B256.toNat_toB256_of_lt hlength256] at h
    simp only [B256.toNat_zero] at h
    omega
  have hstorAssignment : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = oldPauser := by
    change (Devm.getStor base sevm.currentTarget).get (assignmentSlot target) =
      oldPauser
    simpa [logicalStorageOfStor, findEntry_assignmentAt hfind] using
      hw.assignments target htargetValid.2
  have hstorArray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target := by
    have h := hw.arrayWords index hindexLt
    rw [findEntry_targetAt hfind, hlast] at h
    change (Devm.getStor base sevm.currentTarget).get
      (arrayEntrySlot next) = target
    simpa [logicalStorageOfStor, next] using h
  have hstorIndex : base.getStorVal sevm.currentTarget (indexSlot target) =
      next := by
    have h := hw.indices target htargetValid.2
    rw [findEntry_oneBasedIndexAt hfind, hlast] at h
    change (Devm.getStor base sevm.currentTarget).get (indexSlot target) = next
    simpa [logicalStorageOfStor, next] using h
  have hstorLength : base.getStorVal sevm.currentTarget arrayLengthSlot =
      next := by
    change (Devm.getStor base sevm.currentTarget).get arrayLengthSlot = next
    simpa [logicalStorageOfStor, next] using hw.lengthWord
  have hpairwise := registryAddressFamilies_pairwise htargetValid.2
    htargetValid.2 holdValid.2
  have hentryNe := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hnextBound
  have hlengthNe := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have htransport : ∀ k : B256, k ≠ countSlot oldPauser →
      k ≠ assignmentSlot target →
      countPost.getStorVal sevm.currentTarget k =
        base.getStorVal sevm.currentTarget k := by
    intro k hcountNe hassignNe
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _ k
        (pairNe hcountNe),
      temporalSloadBase_getStorVal,
      temporalSstorePost_other _ _ (assignmentSlot target) 0 _ k
        (pairNe hassignNe),
      temporalSloadBase_getStorVal]
  have harray : countPost.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target := by
    rw [htransport _ (Ne.symm hentryNe.2.2) (Ne.symm hentryNe.1)]
    exact hstorArray
  have hindexVal : countPost.getStorVal sevm.currentTarget
      (indexSlot target) = next := by
    rw [htransport _ hpairwise.2.2 (Ne.symm hpairwise.1)]
    exact hstorIndex
  have hlengthVal : countPost.getStorVal sevm.currentTarget arrayLengthSlot =
      next := by
    rw [htransport _ (Ne.symm hlengthNe.2.2) (Ne.symm hlengthNe.1)]
    exact hstorLength
  have hcountVal : countPost.getStorVal sevm.currentTarget
      (countSlot oldPauser) = oldCount - 1 := by
    dsimp only [countPost]
    exact temporalSstorePost_self _ _ _ _
  have hwarmTransport : ∀ k : B256,
      (sevm.currentTarget, k) ∈ base.accessedStorageKeys →
      (sevm.currentTarget, k) ∈ countPost.accessedStorageKeys := by
    intro k hk
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_accessedStorageKeys]
    refine temporalSloadBase_preserves_warm _ _ _ _ ?_
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm _ _ _ _ hk
  have hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      countPost.accessedStorageKeys := by
    dsimp only [countPost]
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_warm _ _ _
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          rw [hsize]
          decide))
  have hsize' : M'.size = 640 := by rw [hsizeM', hsize]
  have htarget' : Bytes.toB256
      (img'.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hprevious' : Bytes.toB256
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser := by
    dsimp only [img']
    rw [show 32 = oldPauser.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hcontinuation' : Bytes.toB256
      (img'.sliceD (continuationWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      decide)]
    exact hcontinuation
  let MIndex := M'.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let post := ((indexClearPost sevm
      (entryClearPost sevm countPost target next)
      target oldLength).addLog eventLog).setMach ⟨[], MLast, G⟩
  have hafterRun := afterOldPauser_foundZeroRetained_runCompiled dp sevm
    countPost M' img' target oldLength next oldPauser (oldCount - 1) []
    (by simp) arrayOriginal indexOriginal lengthOriginal holeCost
    movedIndexCost tailClearCost lengthRestoreCost indexClearCost G
    hwf' hreads' htarget' hprevious' hnew' hcontinuation' htargetValid
    holdValid hremaining hnextNonzero hnextBound 640 3 3 hsize'
    (by rw [hsize']) (by decide) (by decide) (by decide) (by decide)
    harray hindexVal hlengthVal hcountVal harrayOrig hindexOrig hlengthOrig
    hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
    hindexClearCost (hwarmTransport _ hwarmArray) (hwarmTransport _ hwarmIndex)
    (hwarmTransport _ hwarmLength) hwarmCount rfl hgasFinal hstatic
  dsimp only at hafterRun
  have hgAfter : G + 2586 + 3 + 3 + holeCost + movedIndexCost +
      tailClearCost + lengthRestoreCost + indexClearCost =
      G + (2592 + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost) := by omega
  rw [hgAfter] at hafterRun
  have hkernel := setPauserKernel_found_runCompiled dp sevm base M img post
    target 0 oldPauser oldCount assignmentOriginal countOriginal
    assignmentCost countCost
    (2592 + holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
      indexClearCost) G
    hwf hreads htarget hnew htargetValid holdValid hsize.symm.le
    (by rw [hsize]) hstorAssignment
    hassignmentOrig hassignmentCost hcount hcountOrig hcountCost
    (by omega) hstatic
    (by
      simpa only [countPost, countBase, assignPost, M', MIndex, MLength,
        MLast, eventLog, post] using hafterRun)
  have hsetPauser : setPauser entries target 0 =
      some (swapPop entries index) := by
    simp [setPauser, htargetValid.1, hfind]
  obtain ⟨trace, htrace⟩ : ∃ trace,
      setPauserSourceTrace entries target 0 = some trace := by
    simp [setPauserSourceTrace, hsetPauser]
  have hrefines := setPauser_sourceTrace_refines_model htargetValid.1 htrace
  have hpostEntries : trace.postEntries = swapPop entries index := by
    rw [hsetPauser] at hrefines
    exact (Option.some.inj hrefines.1).symm
  have hwpost := hw.applySetPauserSourceTrace htargetValid.2 hzeroCanonical
    htrace
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, rfl, ?_, ?_⟩
  · have hgTotal : G + foundZeroRetainedLastSetPauserKernelGas sevm base target
          oldPauser assignmentCost countCost holeCost movedIndexCost
          tailClearCost lengthRestoreCost indexClearCost =
        G + (2592 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) +
          foundSetPauserKernelPrefixGas sevm base target 0 oldPauser
            assignmentCost countCost := by
      dsimp only [foundZeroRetainedLastSetPauserKernelGas,
        foundSetPauserKernelPrefixGas]
      omega
    rw [hgTotal]
    exact hkernel
  · have logs_setMach (d : Devm) (mach : Mach) :
        (d.setMach mach).logs = d.logs := rfl
    have logs_addLog (d : Devm) (log : Log) :
        (d.addLog log).logs = d.logs ++ [log] := rfl
    dsimp only [post, countPost, countBase, assignPost,
      assignmentPost, assignmentBase, eventLog]
    rw [logs_setMach, logs_addLog]
    congr 1
    simp only [indexClearPost, lengthWritePost,
      entryClearPost, indexWritePost, entryWritePost,
      temporalSstorePost_logs, temporalSloadBase_logs]
  · intro pauser hpauser
    have hexpiryArray := expirySlot_ne_arrayFamily hpauser hnextBound
    have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
      hpauser htargetValid.2 holdValid.2
    calc
      post.getStorVal sevm.currentTarget (expirySlot pauser) =
          (indexClearPost sevm
            (entryClearPost sevm countPost target next)
            target oldLength).getStorVal sevm.currentTarget
              (expirySlot pauser) := rfl
      _ = base.getStorVal sevm.currentTarget (expirySlot pauser) := by
        dsimp only [countPost, countBase, assignPost, assignmentPost,
          assignmentBase]
        simp only [indexClearPost, lengthWritePost,
          entryClearPost, indexWritePost,
          entryWritePost]
        rw [temporalSstorePost_other _ _ (indexSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.1),
          temporalSstorePost_other _ _ arrayLengthSlot oldLength _
            (expirySlot pauser) (pairNe hexpiryArray.1),
          temporalSstorePost_other _ _ (arrayEntrySlot next) 0 _
            (expirySlot pauser) (pairNe hexpiryArray.2),
          temporalSstorePost_other _ _ (indexSlot target) next _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.1),
          temporalSstorePost_other _ _ (arrayEntrySlot next) target _
            (expirySlot pauser) (pairNe hexpiryArray.2),
          temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.2),
          temporalSloadBase_getStorVal,
          temporalSstorePost_other _ _ (assignmentSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.1),
          temporalSloadBase_getStorVal]

/-! ## Shared production-body prefix

`func_run` can traverse this prefix in one shot, but elaborating the resulting
proof term exceeds Lean's default recursion depth.  Keep each computational
step behind a named theorem boundary where its exact successor state is already
known; the composed proof then checks at the default resource limits and is
shared by the four zero-pauser chronology leaves below. -/

private theorem pushNotZero_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {tail : Func} {post : Devm} {target : B256}
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨~~~(0 : B256) :: target :: [], M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨target :: [], M, G + 5⟩)
      ([pushB256 0, not] +++ tail) post := by
  func_run (2) [~~~(0 : B256)]
  case a => exact htail

private theorem shiftAddressMask_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {tail : Func} {post : Devm} {target : B256}
    (htail : Func.RunCompiled fs sevm
      (base.setMach
        ⟨((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) :: target :: [],
          M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨~~~(0 : B256) :: target :: [], M, G + 6⟩)
      ([pushB256 (Nat.toB256 160), shl] +++ tail) post := by
  func_run (2)
    [((~~~(0 : B256)) <<< (Nat.toB256 160).toNat)]
  case a => exact htail

private theorem canonicalBranch_success_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (hmask : addressMask &&& target = 0)
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G⟩) body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨addressMask :: target :: [], M, G + 16⟩)
      ([Ninst.and] +++ ((.call emptyRevertSlot) <?> body)) post := by
  func_run (2) [0]
  case h_arm =>
    have hg : G + 16 - 16 = G := by omega
    rw [hg]
    exact hbody

private theorem checkNonAddress_success_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (hmask : addressMask &&& target = 0)
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G⟩) body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨target :: [], M, G + 27⟩)
      (checkNonAddress +++ ((.call emptyRevertSlot) <?> body)) post := by
  have hbranch := canonicalBranch_success_runCompiled hmask hbody
  have hshiftRaw :
      Func.RunCompiled fs sevm
        (base.setMach
          ⟨((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) :: target :: [],
            M, G + 16⟩)
        ([Ninst.and] +++ ((.call emptyRevertSlot) <?> body)) post := by
    rw [← addressMask_eq_shl]
    exact hbranch
  have hshift := shiftAddressMask_prepend_runCompiled hshiftRaw
  have hnot := pushNotZero_prepend_runCompiled hshift
  have hg : G + 16 + 6 + 5 = G + 27 := by omega
  have hsplit :
      checkNonAddress +++ ((.call emptyRevertSlot) <?> body) =
        [pushB256 0, not] +++
          ([pushB256 (Nat.toB256 160), shl] +++
            ([Ninst.and] +++ ((.call emptyRevertSlot) <?> body))) := by
    rfl
  rw [← hg, hsplit]
  exact hnot

private theorem arg0_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {tail : Func} {post : Devm} {target : B256}
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨target :: [], M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + 6⟩)
      (arg 0 +++ tail) post := by
  unfold arg cdl
  func_run (2)
  case a => rw [harg]; exact htail

private theorem arg1_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {tail : Func} {post : Devm} {target : B256}
    (harg : Sevm.dataWord sevm (32 * 1 + 4) = target)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨target :: [], M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + 6⟩)
      (arg 1 +++ tail) post := by
  unfold arg cdl
  func_run (2)
  case a => rw [harg]; exact htail

private theorem canonicalAddressArg0_success_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hmask : addressMask &&& target = 0)
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G⟩) body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + 33⟩)
      (canonicalAddressArg 0 body) post := by
  have hcheck := checkNonAddress_success_runCompiled hmask hbody
  have hargRun := arg0_prepend_runCompiled harg hcheck
  have hg : G + 27 + 6 = G + 33 := by omega
  have hsplit :
      canonicalAddressArg 0 body =
        arg 0 +++
          (checkNonAddress +++ ((.call emptyRevertSlot) <?> body)) := by
    rfl
  rw [← hg, hsplit]
  exact hargRun

private theorem canonicalAddressArg1_success_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (harg : Sevm.dataWord sevm (32 * 1 + 4) = target)
    (hmask : addressMask &&& target = 0)
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G⟩) body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + 33⟩)
      (canonicalAddressArg 1 body) post := by
  have hcheck := checkNonAddress_success_runCompiled hmask hbody
  have hargRun := arg1_prepend_runCompiled harg hcheck
  have hg : G + 27 + 6 = G + 33 := by omega
  have hsplit :
      canonicalAddressArg 1 body =
        arg 1 +++
          (checkNonAddress +++ ((.call emptyRevertSlot) <?> body)) := by
    rfl
  rw [← hg, hsplit]
  exact hargRun

private theorem requireStaticArgs_success_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {G : Nat} {body : Func} {post : Devm}
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G⟩) body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + 21⟩)
      (requireStaticArgs 2 body) post := by
  unfold requireStaticArgs
  func_run (4) [0]
  case h_arm =>
    have hg : G + 21 - 21 = G := by omega
    rw [hg]
    exact hbody

private theorem onlyAdmin_success_runCompiled
    {fs : List Func} {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {M : Mem} {G : Nat} {body : Func} {post : Devm}
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G⟩) body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + 22⟩)
      (onlyAdmin dp body) post := by
  unfold onlyAdmin pushDeployWord
  func_run (4) [1]
  case h_val => simp [hadmin, B256.eqCheck]
  case h_arm => simpa using hbody

private theorem registerPauser_body_from_kernel_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target : B256) (kernelGas : Nat) (post : Devm)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (htargetMask : addressMask &&& target = 0)
    (hnewMask : addressMask &&& (0 : B256) = 0)
    (hkernel : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], registerMemory target 0, kernelGas⟩)
      setPauserKernel post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, kernelGas + 221⟩)
      (registerPauser dp) post := by
  have hstage := registerPauser_stageArgs_runCompiled dp sevm base target 0
    kernelGas post hargTarget hargNew hkernel
  have hadminRun := onlyAdmin_success_runCompiled hadmin hstage
  have hnewRun :=
    canonicalAddressArg1_success_runCompiled hargNew hnewMask hadminRun
  have htargetRun :=
    canonicalAddressArg0_success_runCompiled hargTarget htargetMask hnewRun
  have hstaticRun :=
    requireStaticArgs_success_runCompiled hdata htargetRun
  have hg :
      ((((kernelGas + 112) + 22) + 33) + 33) + 21 =
        kernelGas + 221 := by
    omega
  rw [← hg]
  simpa only [registerPauser] using hstaticRun

/-- Exact production-body reserve for unregistering a recorded target that is
already the array's last entry, with the old pauser retained. -/
def foundZeroRetainedLastRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost : Nat) : Nat :=
  221 + foundZeroRetainedLastSetPauserKernelGas sevm base target oldPauser
    assignmentCost countCost holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost

/-- Exact successful production body for unregistering a recorded target under
the two restrictions the removal machinery supports: the removed target is
already the array's last entry (`index + 1 = entries.length`), and the old
pauser is retained (`oldCount - 1 ≠ 0`), so `registerAfterSet` stops without
touching any expiry slot. -/
theorem registerPauser_body_foundZeroRetainedLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + foundZeroRetainedLastRegisterBodyGas sevm base target oldPauser
            assignmentCost countCost holeCost movedIndexCost tailClearCost
            lengthRestoreCost indexClearCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  rcases registerMemory_spec target 0 with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      _hpreviousRead, hcontinuationRead⟩
  rcases setPauserKernel_foundZeroRetainedLast_runCompiled dp sevm base
      (registerMemory target 0) (registerImage target 0)
      entries target index oldPauser oldCount assignmentOriginal countOriginal
      arrayOriginal indexOriginal lengthOriginal assignmentCost countCost
      holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost G
      hw hfind hlast hwf hreads htargetRead hnewRead hcontinuationRead
      htargetValid holdValid hsize hassignmentOrig hassignmentCost hcount
      hcountOrig hcountCost hremaining harrayOrig hindexOrig hlengthOrig
      hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
      hindexClearCost hwarmArray hwarmIndex hwarmLength hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hkernel, hgas, hlogs,
      hexpiries⟩
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, hgas, hlogs,
    hexpiries⟩
  have htargetMask := canonicalAddress_mask_zero htargetValid.2
  have hnewMask : addressMask &&& (0 : B256) = 0 := by decide +kernel
  have hbody := registerPauser_body_from_kernel_runCompiled dp sevm base target
    (G + foundZeroRetainedLastSetPauserKernelGas sevm base target oldPauser
      assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost) post hdata hadmin hargTarget hargNew
    htargetMask hnewMask hkernel
  simp only [foundZeroRetainedLastRegisterBodyGas]
  have hg :
      G + (221 + foundZeroRetainedLastSetPauserKernelGas sevm base target
        oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost) =
      (G + foundZeroRetainedLastSetPauserKernelGas sevm base target oldPauser
        assignmentCost countCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost) + 221 := by
    omega
  rw [hg]
  exact hbody

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-runtime success for unregistering a recorded target under
the two restrictions the removal machinery supports: the removed target is
already the array's last entry (`index + 1 = entries.length`), and the old
pauser is retained (`oldCount - 1 ≠ 0`), so `registerAfterSet` stops without
touching any expiry slot. -/
theorem registerPauser_runCompiledTo_foundZeroRetainedLast
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            foundZeroRetainedLastRegisterBodyGas sevm base target oldPauser
              assignmentCost countCost holeCost movedIndexCost tailClearCost
              lengthRestoreCost indexClearCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      (∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_foundZeroRetainedLast_runCompiled dp sevm base
      entries target index oldPauser oldCount assignmentOriginal countOriginal
      arrayOriginal indexOriginal lengthOriginal assignmentCost countCost
      holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost G
      hbodyData hadmin hargTarget hargNew hw hfind hlast htargetValid holdValid
      hassignmentOrig hassignmentCost hcount hcountOrig hcountCost hremaining
      harrayOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost
      htailClearCost hlengthRestoreCost hindexClearCost hwarmArray hwarmIndex
      hwarmLength hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hbody, hgas, hlogs,
      hexpiries⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (foundZeroRetainedLastRegisterBodyGas sevm base target oldPauser
        assignmentCost countCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
    hexpiries, hcompile⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact clean direct-message effects for unregistering a recorded target,
derived from the generated-runtime execution.  Both restrictions of the
removal chronology are inherited: the removed target is already the array's
last entry (`index + 1 = entries.length`), and the old pauser is retained
(`oldCount - 1 ≠ 0`), so no expiry slot moves. -/
theorem registerPauser_foundZeroRetainedLast_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr} {final settled : Devm}
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target 0)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      foundZeroRetainedLastRegisterBodyGas (initSevm msg) (initDevm msg)
        target oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor (initDevm msg) ca)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost (initSevm msg) (initDevm msg)
      target 0).getStorVal ca (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (harrayOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal (initSevm msg) ca arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (ca, arrayEntrySlot (Nat.toB256 entries.length)) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmIndex : (ca, indexSlot target) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmLength : (ca, arrayLengthSlot) ∈
      (initDevm msg).accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : (initSevm msg).isStatic = false)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    ∃ trace,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor (initDevm msg) ca) trace.writes))
        trace.postEntries ∧
      settled.gasLeft = G ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        settled.getStorVal ca (expirySlot pauser) =
          (initDevm msg).getStorVal ca (expirySlot pauser) := by
  have hdataInit : (initSevm msg).data =
      registerPauserCalldata target 0 := by
    simpa [initSevm] using hdata
  rcases registerPauserCalldata_spec (initSevm msg) target 0 hdataInit with
    ⟨hdataLength, hselector, hargTarget, hargNew⟩
  have hvalueInit : (initSevm msg).value = 0 := by
    simpa [initSevm] using hvalue
  have hownerInit : (initSevm msg).currentTarget = ca := by
    simpa [initSevm] using howner
  have hcodeAddressInit : (initSevm msg).codeAddress =
      some (initSevm msg).currentTarget := by
    simpa [initSevm, howner] using hcodeAddress
  have hcodeInit : (initSevm msg).code.toList =
      lidoCircuitBreakerCode dp := by
    simpa [initSevm] using hcode
  have hadminInit : (initSevm msg).caller.toB256 = dp.admin := by
    simpa [initSevm] using hadmin
  rcases registerPauser_runCompiledTo_foundZeroRetainedLast dp (initSevm msg)
      (initDevm msg) entries target index oldPauser oldCount
      assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal assignmentCost countCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost G hdataLength hvalueInit
      hselector hcodeAddressInit hcodeInit hadminInit hargTarget hargNew
      (by simpa [hownerInit] using hw) hfind hlast htargetValid holdValid
      (by simpa [hownerInit] using hassignmentOrig) hassignmentCost
      (by simpa [hownerInit] using hcount)
      (by simpa [hownerInit] using hcountOrig) hcountCost hremaining
      (by simpa [hownerInit] using harrayOrig)
      (by simpa [hownerInit] using hindexOrig)
      (by simpa [hownerInit] using hlengthOrig) hholeCost hmovedIndexCost
      htailClearCost hlengthRestoreCost hindexClearCost
      (by simpa [hownerInit] using hwarmArray)
      (by simpa [hownerInit] using hwarmIndex)
      (by simpa [hownerInit] using hwarmLength) hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
      hexpiries, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          foundZeroRetainedLastRegisterBodyGas (initSevm msg) (initDevm msg)
            target oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost⟩ =
        initDevm msg := by
    rw [← hgasEntry]
    rfl
  have hrunEntry : Prog.RunCompiledTo (initSevm msg) (initDevm msg)
      (runtime dp) (.ok post) := by
    rw [hentryState] at hrun
    exact hrun
  have hexecEq : exec ⟨0, initSevm msg, initDevm msg⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrunEntry hcompile
  obtain ⟨hpostExec⟩ :=
    (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok post)).mpr
      hexecEq
  change Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hsettledFinal := registerPauser_success_settles_cleanly dp
    htargetOwner howner hcodeAddress hcode hvalue hdata hprocess hclean
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  refine ⟨trace, htrace, hpostEntries, ?_, hgas, ?_, ?_⟩
  · simpa [hownerInit] using hwpost
  · simpa [hownerInit] using hlogs
  · intro pauser hpauser
    simpa [hownerInit] using hexpiries pauser hpauser

/-! ## Found-target zero-pauser registration removing an interior entry

The same chronology-3 leaf with the removal restriction lifted: the removed
target is **not** the array's last entry, so the general swap-and-pop walk
`removeTarget_swapPop_runCompiled` moves the last entry into the hole and
repairs its reverse index.  The old pauser is still retained. -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The general swap-and-pop removal at the found-target/zero-pauser leaf: the
removed target sits at `idx`, the array's last entry is `lastTarget` at `len`,
and the old pauser is retained, so `finishSetPauser` stops without touching any
expiry slot.  The old pauser's count survives all five array-region writes. -/
private theorem removeTarget_foundZeroRetainedSwapPop_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength oldPauser remaining : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hlastValid : canonicalAddress lastTarget)
    (hlastNe : lastTarget ≠ target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hremaining : remaining ≠ 0)
    (hidxNonzero : idx ≠ 0) (hidxBound : idx.toNat < 2 ^ 252)
    (hlenNonzero : len ≠ 0) (hlenBound : len.toNat < 2 ^ 252)
    (hidxNeLen : idx ≠ len)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (hhole : base.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = holeCurrent)
    (hmoved : base.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = movedCurrent)
    (htail : base.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget)
    (hindex : base.getStorVal sevm.currentTarget (indexSlot target) = idx)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = len)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot idx) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot lastTarget) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot len) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal holeCurrent lastTarget =
      holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal movedCurrent idx =
      movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal lastTarget 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal len oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal idx 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget, arrayEntrySlot idx) ∈
      base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget, indexSlot lastTarget) ∈
      base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget, arrayEntrySlot len) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : len - 1 = oldLength)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 2551 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost⟩)
      removeTarget
      (((indexClearPost sevm
          (swapPopClearPost sevm base lastTarget idx len)
          target oldLength).addLog eventLog).setMach
        ⟨stack, MLast, G⟩) := by
  dsimp only
  let countKey := countSlot oldPauser
  let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    lastTarget.toBytes
  let tailPost := swapPopClearPost sevm base lastTarget idx len
  let removePost := indexClearPost sevm tailPost target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  have hwfIndex : Mem.Wf MIndex := hwf.write _ _
  have hreadsIndex : Mem.Reads MIndex imgIndex :=
    Mem.Reads.write hwf hreads _ _
  have hwfLength : Mem.Wf MLength := hwfIndex.write _ _
  have hreadsLength : Mem.Reads MLength imgLength :=
    Mem.Reads.write hwfIndex hreadsIndex _ _
  have hreadsLast : Mem.Reads MLast imgLast :=
    Mem.Reads.write hwfLength hreadsLength _ _
  have hsizeIndex : MIndex.size = max entrySize 672 := by
    dsimp only [MIndex]
    rw [Mem.size_write_word_at,
      show (removedIndexWord * 32).toNat + 32 = 672 by decide, hsize,
      show ceil32 672 = 672 by decide]
    split <;> omega
  have hsizeLength : MLength.size = 704 := by
    dsimp only [MLength]
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide,
      hsizeIndex, show ceil32 704 = 704 by decide]
    split <;> omega
  have hsizeLast : MLast.size = 736 := by
    dsimp only [MLast]
    rw [Mem.size_write_word_at,
      show (lastTargetWord * 32).toNat + 32 = 736 by decide,
      hsizeLength]
    split
    · omega
    · decide
  have halignIndex : MIndex.size % 32 = 0 :=
    Mem.aligned_write_word halign
  have halignLength : MLength.size % 32 = 0 :=
    Mem.aligned_write_word halignIndex
  have halignLast : MLast.size % 32 = 0 :=
    Mem.aligned_write_word halignLength
  have earlierLast {word : B256}
      (hindexBefore : (word * 32).toNat + 32 ≤
        (removedIndexWord * 32).toNat)
      (hlengthBefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat)
      (hlastBefore : (word * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat) :
      Bytes.toB256 (imgLast.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlastBefore]
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlengthBefore]
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hindexBefore]
  have htargetLast : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target :=
    (earlierLast (by decide) (by decide) (by decide)).trans htarget
  have hpreviousLast : Bytes.toB256
      (imgLast.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser :=
    (earlierLast (by decide) (by decide) (by decide)).trans hprevious
  have hnewLast : Bytes.toB256
      (imgLast.sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hnew
  have hcontinuationLast : Bytes.toB256
      (imgLast.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hcontinuation
  have hidxFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hidxBound
  have hlenFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hlenBound
  have hpairs := registryAddressFamilies_pairwise
    htargetValid.2 htargetValid.2 holdValid.2
  have hlastPairs := registryAddressFamilies_pairwise
    htargetValid.2 hlastValid holdValid.2
  have hlengthCount := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have hcountRemove : removePost.getStorVal sevm.currentTarget countKey =
      remaining := by
    simp only [removePost, tailPost, indexClearPost, lengthWritePost,
      swapPopClearPost, indexWritePost, entryWritePost]
    rw [temporalSstorePost_other _ _ (indexSlot target) 0 _ countKey
        (pairNe (Ne.symm hpairs.2.2)),
      temporalSstorePost_other _ _ arrayLengthSlot oldLength _ countKey
        (pairNe hlengthCount.2.2),
      temporalSstorePost_other _ _ (arrayEntrySlot len) 0 _ countKey
        (pairNe hlenFamilies.2.2),
      temporalSstorePost_other _ _ (indexSlot lastTarget) idx _ countKey
        (pairNe (Ne.symm hlastPairs.2.2)),
      temporalSstorePost_other _ _ (arrayEntrySlot idx) lastTarget _ countKey
        (pairNe hidxFamilies.2.2)]
    exact hcount
  have hwarmCountRemove : (sevm.currentTarget, countKey) ∈
      removePost.accessedStorageKeys := by
    simp only [removePost, tailPost, indexClearPost, lengthWritePost,
      swapPopClearPost, indexWritePost, entryWritePost,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmCount
  have hfinish := finishSetPauser_retainedOldZero_runCompiled dp sevm
    removePost MLast imgLast target oldPauser remaining stack G hstack
    hreadsLast htargetLast hpreviousLast hnewLast hcontinuationLast
    holdValid.1 hremaining (by simpa only [countKey] using hcountRemove)
    (by simpa only [countKey] using hwarmCountRemove)
    (by rw [hsizeLast]; decide) halignLast hstatic
  have hrun := removeTarget_swapPop_runCompiled dp sevm base M img
    target lastTarget idx len oldLength oldPauser stack hstack
    holeCurrent movedCurrent holeOriginal movedOriginal tailOriginal
    lengthOriginal indexOriginal holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost 2108 G hwf hreads htarget htargetValid
    hlastValid hlastNe hidxNonzero hidxBound hlenNonzero hlenBound hidxNeLen
    entrySize indexExtCost lengthExtCost 4 hsize halign hentryLow
    hindexExtCost hlengthExtCost
    (by rw [Nat.max_eq_right hentryHigh]; decide)
    hhole hmoved htail hindex hlength
    hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig hholeCost
    hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    hwarmHole hwarmMoved hwarmTail hwarmIndex hwarmLength hsub hgasFinal
    hstatic
    (by simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog]
      using hfinish)
  have hg : G + 2108 + 439 + 4 + indexExtCost + lengthExtCost + holeCost +
      movedIndexCost + tailClearCost +
      lengthRestoreCost + indexClearCost =
      G + 2551 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost := by omega
  rw [hg] at hrun
  simpa only [MIndex, MLength, MLast, eventLog] using hrun

/-- The `afterOldPauser` glue above the general swap-and-pop removal: the
new-pauser scratch word is zero, so the walk branches straight to
`removeTarget` for 35 gas. -/
private theorem afterOldPauser_foundZeroRetainedSwapPop_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength oldPauser remaining : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hlastValid : canonicalAddress lastTarget)
    (hlastNe : lastTarget ≠ target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hremaining : remaining ≠ 0)
    (hidxNonzero : idx ≠ 0) (hidxBound : idx.toNat < 2 ^ 252)
    (hlenNonzero : len ≠ 0) (hlenBound : len.toNat < 2 ^ 252)
    (hidxNeLen : idx ≠ len)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (hhole : base.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = holeCurrent)
    (hmoved : base.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = movedCurrent)
    (htail : base.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget)
    (hindex : base.getStorVal sevm.currentTarget (indexSlot target) = idx)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = len)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot idx) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot lastTarget) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot len) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal holeCurrent lastTarget =
      holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal movedCurrent idx =
      movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal lastTarget 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal len oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal idx 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget, arrayEntrySlot idx) ∈
      base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget, indexSlot lastTarget) ∈
      base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget, arrayEntrySlot len) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : len - 1 = oldLength)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 2586 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost⟩)
      afterOldPauser
      (((indexClearPost sevm
          (swapPopClearPost sevm base lastTarget idx len)
          target oldLength).addLog eventLog).setMach
        ⟨stack, MLast, G⟩) := by
  dsimp only
  let fs := (runtime dp).main :: (runtime dp).aux
  let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  have hremove := removeTarget_foundZeroRetainedSwapPop_runCompiled dp sevm
    base M img target lastTarget idx len oldLength oldPauser remaining stack
    hstack holeCurrent movedCurrent holeOriginal movedOriginal tailOriginal
    lengthOriginal indexOriginal holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost G hwf hreads htarget hprevious hnew
    hcontinuation htargetValid hlastValid hlastNe holdValid hremaining
    hidxNonzero hidxBound hlenNonzero hlenBound hidxNeLen
    entrySize indexExtCost lengthExtCost hsize halign hentryLow hentryHigh
    hindexExtCost hlengthExtCost hhole hmoved htail hindex hlength hcount
    hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig hholeCost
    hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    hwarmHole hwarmMoved hwarmTail hwarmIndex hwarmLength hwarmCount hsub
    hgasFinal hstatic
  have h := afterOldPauser_removeTarget_runCompiled dp sevm base M img
    stack
    (G + 2551 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
      tailClearCost + lengthRestoreCost + indexClearCost)
    (((indexClearPost sevm
        (swapPopClearPost sevm base lastTarget idx len)
        target oldLength).addLog eventLog).setMach ⟨stack, MLast, G⟩)
    hstack hreads hnew (by omega) halign
    (by simpa only [fs, MIndex, MLength, MLast, eventLog] using hremove)
  have hg : G + 2551 + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost + 35 =
      G + 2586 + indexExtCost + lengthExtCost + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost := by omega
  rw [hg] at h
  exact h

/-- Exact reserve for the found-target/zero-pauser kernel when the removed
target is **not** the array's last entry and the old pauser is retained.  Same
shape as the degenerate row: the actual assignment and count SLOAD costs, the
seven exact SSTORE value-cost partitions, and the fixed removal-walk memory
growth at a 640-byte entry size.  The general swap-and-pop walk costs the same
443 gas above `finishSetPauser` as the degenerate one; only the five SSTORE
value-cost partitions differ, and those are parameters. -/
private def foundZeroRetainedSwapPopSetPauserKernelGas (sevm : Sevm)
    (base : Devm) (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost : Nat) : Nat :=
  2714 + temporalSloadCost sevm base (assignmentSlot target) + assignmentCost +
    temporalSloadCost sevm (assignmentPost sevm base target 0)
      (countSlot oldPauser) + countCost + holeCost + movedIndexCost +
    tailClearCost + lengthRestoreCost + indexClearCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-kernel success for unregistering a recorded target that is
**not** the array's last entry, with the old pauser retained.  This is the
consumer of the general swap-and-pop removal walk: the last array entry
`sourceLastTarget entries` is moved into the removed target's hole at
`index + 1` and its reverse index is repaired, the vacated tail at
`entries.length` is cleared, the length is decremented and the removed target's
index is cleared.  Binding the substrate's abstract `lastTarget` to the model's
`sourceLastTarget entries` is done here, out of the `RegistryWitness`; the
substrate walk is chronology-independent and knows nothing about `entries`.

The old pauser is retained (`oldCount - 1 ≠ 0`), so `registerAfterSet` takes
the else arm and, seeing a zero new pauser, stops without touching any expiry
slot. -/
theorem setPauserKernel_foundZeroRetainedSwapPop_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (entries : List Entry) (target : B256)
    (index : Nat) (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hsize : M.size = 640)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (index + 1))) ∈ base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget,
      indexSlot (sourceLastTarget entries)) ∈ base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M,
          G + foundZeroRetainedSwapPopSetPauserKernelGas sevm base target
            oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost⟩)
        setPauserKernel post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have hindexLt : index < entries.length := findEntry_index_lt hfind
  obtain ⟨lastEntry, hlast⟩ := last_some_of_findEntry hfind
  have hlastMem := last_mem_of_last entries hlast
  have hlastEntryValid := hw.targetsValid lastEntry hlastMem
  have hsourceLast : sourceLastTarget entries = lastEntry.1 := by
    simp [sourceLastTarget, hlast]
  have hlastValid : canonicalAddress (sourceLastTarget entries) := by
    rw [hsourceLast]
    exact hlastEntryValid.2
  have hlastAt : oneBasedIndexAt entries (sourceLastTarget entries) =
      entries.length := by
    have hone := oneBasedIndexAt_targetAt_of_lt entries hw.targetsNodup
      (show entries.length - 1 < entries.length by omega)
    rw [targetAt_last_of_last entries hlast] at hone
    rw [hsourceLast, hone]
    omega
  have hlastNe : sourceLastTarget entries ≠ target := by
    intro heq
    have hone : oneBasedIndexAt entries target = entries.length := by
      rw [← heq]
      exact hlastAt
    rw [findEntry_oneBasedIndexAt hfind] at hone
    omega
  let idx : B256 := Nat.toB256 (index + 1)
  let len : B256 := Nat.toB256 entries.length
  let lastTarget : B256 := sourceLastTarget entries
  let oldLength : B256 := len - 1
  let assignPost := assignmentPost sevm base target 0
  let countBase := temporalSloadBase sevm assignPost (countSlot oldPauser)
  let countPost := temporalSstorePost sevm countBase (countSlot oldPauser)
    (oldCount - 1)
  let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    oldPauser.toBytes
  have hlength256 := hw.entries_length_lt_2pow256
  have hlength252 := hw.entries_length_lt_2pow252
  have hlenBound : len.toNat < 2 ^ 252 := by
    dsimp only [len]
    rw [B256.toNat_toB256_of_lt hlength256]
    exact hlength252
  have hlenNonzero : len ≠ 0 := by
    intro hz
    have h := congrArg B256.toNat hz
    rw [show len = Nat.toB256 entries.length from rfl,
      B256.toNat_toB256_of_lt hlength256] at h
    simp only [B256.toNat_zero] at h
    omega
  have hidxBound : idx.toNat < 2 ^ 252 := by
    dsimp only [idx]
    rw [B256.toNat_toB256_of_lt (by omega)]
    omega
  have hidxNonzero : idx ≠ 0 := by
    intro hz
    have h := congrArg B256.toNat hz
    rw [show idx = Nat.toB256 (index + 1) from rfl,
      B256.toNat_toB256_of_lt (by omega)] at h
    simp only [B256.toNat_zero] at h
    omega
  have hidxNeLen : idx ≠ len := by
    intro heq
    exact absurd
      (natToB256_injective_of_lt (by omega) hlength256 heq) (by omega)
  have hstorAssignment : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = oldPauser := by
    change (Devm.getStor base sevm.currentTarget).get (assignmentSlot target) =
      oldPauser
    simpa [logicalStorageOfStor, findEntry_assignmentAt hfind] using
      hw.assignments target htargetValid.2
  have hstorHole : base.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = target := by
    have h := hw.arrayWords index hindexLt
    rw [findEntry_targetAt hfind] at h
    change (Devm.getStor base sevm.currentTarget).get (arrayEntrySlot idx) =
      target
    simpa [logicalStorageOfStor, idx] using h
  have hstorTail : base.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget := by
    have h := hw.arrayWords (entries.length - 1) (by omega)
    rw [targetAt_last_of_last entries hlast,
      show entries.length - 1 + 1 = entries.length by omega] at h
    change (Devm.getStor base sevm.currentTarget).get (arrayEntrySlot len) =
      lastTarget
    simpa [logicalStorageOfStor, len, lastTarget, hsourceLast] using h
  have hstorMoved : base.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = len := by
    have h := hw.indices lastTarget hlastValid
    rw [hlastAt] at h
    change (Devm.getStor base sevm.currentTarget).get (indexSlot lastTarget) =
      len
    simpa [logicalStorageOfStor, len] using h
  have hstorIndex : base.getStorVal sevm.currentTarget (indexSlot target) =
      idx := by
    have h := hw.indices target htargetValid.2
    rw [findEntry_oneBasedIndexAt hfind] at h
    change (Devm.getStor base sevm.currentTarget).get (indexSlot target) = idx
    simpa [logicalStorageOfStor, idx] using h
  have hstorLength : base.getStorVal sevm.currentTarget arrayLengthSlot =
      len := by
    change (Devm.getStor base sevm.currentTarget).get arrayLengthSlot = len
    simpa [logicalStorageOfStor, len] using hw.lengthWord
  have hpairwise := registryAddressFamilies_pairwise htargetValid.2
    htargetValid.2 holdValid.2
  have hlastPairs := registryAddressFamilies_pairwise htargetValid.2
    hlastValid holdValid.2
  have hidxFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hidxBound
  have hlenFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hlenBound
  have hlengthNe := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have htransport : ∀ k : B256, k ≠ countSlot oldPauser →
      k ≠ assignmentSlot target →
      countPost.getStorVal sevm.currentTarget k =
        base.getStorVal sevm.currentTarget k := by
    intro k hcountNe hassignNe
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _ k
        (pairNe hcountNe),
      temporalSloadBase_getStorVal,
      temporalSstorePost_other _ _ (assignmentSlot target) 0 _ k
        (pairNe hassignNe),
      temporalSloadBase_getStorVal]
  have hhole : countPost.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = target := by
    rw [htransport _ (Ne.symm hidxFamilies.2.2) (Ne.symm hidxFamilies.1)]
    exact hstorHole
  have hmoved : countPost.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = len := by
    rw [htransport _ hlastPairs.2.2 (Ne.symm hlastPairs.1)]
    exact hstorMoved
  have htail : countPost.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget := by
    rw [htransport _ (Ne.symm hlenFamilies.2.2) (Ne.symm hlenFamilies.1)]
    exact hstorTail
  have hindexVal : countPost.getStorVal sevm.currentTarget
      (indexSlot target) = idx := by
    rw [htransport _ hpairwise.2.2 (Ne.symm hpairwise.1)]
    exact hstorIndex
  have hlengthVal : countPost.getStorVal sevm.currentTarget arrayLengthSlot =
      len := by
    rw [htransport _ (Ne.symm hlengthNe.2.2) (Ne.symm hlengthNe.1)]
    exact hstorLength
  have hcountVal : countPost.getStorVal sevm.currentTarget
      (countSlot oldPauser) = oldCount - 1 := by
    dsimp only [countPost]
    exact temporalSstorePost_self _ _ _ _
  have hwarmTransport : ∀ k : B256,
      (sevm.currentTarget, k) ∈ base.accessedStorageKeys →
      (sevm.currentTarget, k) ∈ countPost.accessedStorageKeys := by
    intro k hk
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_accessedStorageKeys]
    refine temporalSloadBase_preserves_warm _ _ _ _ ?_
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm _ _ _ _ hk
  have hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      countPost.accessedStorageKeys := by
    dsimp only [countPost]
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_warm _ _ _
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          rw [hsize]
          decide))
  have hsize' : M'.size = 640 := by rw [hsizeM', hsize]
  have htarget' : Bytes.toB256
      (img'.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hprevious' : Bytes.toB256
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser := by
    dsimp only [img']
    rw [show 32 = oldPauser.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hcontinuation' : Bytes.toB256
      (img'.sliceD (continuationWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      decide)]
    exact hcontinuation
  let MIndex := M'.write (removedIndexWord * 32).toNat idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let post := ((indexClearPost sevm
      (swapPopClearPost sevm countPost lastTarget idx len)
      target oldLength).addLog eventLog).setMach ⟨[], MLast, G⟩
  have hafterRun := afterOldPauser_foundZeroRetainedSwapPop_runCompiled dp sevm
    countPost M' img' target lastTarget idx len oldLength oldPauser
    (oldCount - 1) [] (by simp) target len holeOriginal movedOriginal
    tailOriginal lengthOriginal indexOriginal holeCost movedIndexCost
    tailClearCost lengthRestoreCost indexClearCost G
    hwf' hreads' htarget' hprevious' hnew' hcontinuation' htargetValid
    hlastValid hlastNe holdValid hremaining hidxNonzero hidxBound hlenNonzero
    hlenBound hidxNeLen 640 3 3 hsize' (by rw [hsize']) (by decide) (by decide)
    (by decide) (by decide) hhole hmoved htail hindexVal hlengthVal hcountVal
    hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig hholeCost
    hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    (hwarmTransport _ hwarmHole) (hwarmTransport _ hwarmMoved)
    (hwarmTransport _ hwarmTail) (hwarmTransport _ hwarmIndex)
    (hwarmTransport _ hwarmLength) hwarmCount rfl hgasFinal hstatic
  dsimp only at hafterRun
  have hgAfter : G + 2586 + 3 + 3 + holeCost + movedIndexCost +
      tailClearCost + lengthRestoreCost + indexClearCost =
      G + (2592 + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost) := by omega
  rw [hgAfter] at hafterRun
  have hkernel := setPauserKernel_found_runCompiled dp sevm base M img post
    target 0 oldPauser oldCount assignmentOriginal countOriginal
    assignmentCost countCost
    (2592 + holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
      indexClearCost) G
    hwf hreads htarget hnew htargetValid holdValid hsize.symm.le
    (by rw [hsize]) hstorAssignment
    hassignmentOrig hassignmentCost hcount hcountOrig hcountCost
    (by omega) hstatic
    (by
      simpa only [countPost, countBase, assignPost, M', MIndex, MLength,
        MLast, eventLog, post] using hafterRun)
  have hsetPauser : setPauser entries target 0 =
      some (swapPop entries index) := by
    simp [setPauser, htargetValid.1, hfind]
  obtain ⟨trace, htrace⟩ : ∃ trace,
      setPauserSourceTrace entries target 0 = some trace := by
    simp [setPauserSourceTrace, hsetPauser]
  have hrefines := setPauser_sourceTrace_refines_model htargetValid.1 htrace
  have hpostEntries : trace.postEntries = swapPop entries index := by
    rw [hsetPauser] at hrefines
    exact (Option.some.inj hrefines.1).symm
  have hwpost := hw.applySetPauserSourceTrace htargetValid.2 hzeroCanonical
    htrace
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, rfl, ?_, ?_⟩
  · have hgTotal : G + foundZeroRetainedSwapPopSetPauserKernelGas sevm base
          target oldPauser assignmentCost countCost holeCost movedIndexCost
          tailClearCost lengthRestoreCost indexClearCost =
        G + (2592 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) +
          foundSetPauserKernelPrefixGas sevm base target 0 oldPauser
            assignmentCost countCost := by
      dsimp only [foundZeroRetainedSwapPopSetPauserKernelGas,
        foundSetPauserKernelPrefixGas]
      omega
    rw [hgTotal]
    exact hkernel
  · have logs_setMach (d : Devm) (mach : Mach) :
        (d.setMach mach).logs = d.logs := rfl
    have logs_addLog (d : Devm) (log : Log) :
        (d.addLog log).logs = d.logs ++ [log] := rfl
    dsimp only [post, countPost, countBase, assignPost,
      assignmentPost, assignmentBase, eventLog]
    rw [logs_setMach, logs_addLog]
    congr 1
    simp only [indexClearPost, lengthWritePost,
      swapPopClearPost, indexWritePost, entryWritePost,
      temporalSstorePost_logs, temporalSloadBase_logs]
  · intro pauser hpauser
    have hexpiryIdx := expirySlot_ne_arrayFamily hpauser hidxBound
    have hexpiryLen := expirySlot_ne_arrayFamily hpauser hlenBound
    have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
      hpauser htargetValid.2 holdValid.2
    have hexpiryLastRegistry := expirySlot_ne_registryAddressFamilies
      hpauser hlastValid holdValid.2
    calc
      post.getStorVal sevm.currentTarget (expirySlot pauser) =
          (indexClearPost sevm
            (swapPopClearPost sevm countPost lastTarget idx len)
            target oldLength).getStorVal sevm.currentTarget
              (expirySlot pauser) := rfl
      _ = base.getStorVal sevm.currentTarget (expirySlot pauser) := by
        dsimp only [countPost, countBase, assignPost, assignmentPost,
          assignmentBase]
        simp only [indexClearPost, lengthWritePost,
          swapPopClearPost, indexWritePost, entryWritePost]
        rw [temporalSstorePost_other _ _ (indexSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.1),
          temporalSstorePost_other _ _ arrayLengthSlot oldLength _
            (expirySlot pauser) (pairNe hexpiryLen.1),
          temporalSstorePost_other _ _ (arrayEntrySlot len) 0 _
            (expirySlot pauser) (pairNe hexpiryLen.2),
          temporalSstorePost_other _ _ (indexSlot lastTarget) idx _
            (expirySlot pauser) (pairNe hexpiryLastRegistry.2.1),
          temporalSstorePost_other _ _ (arrayEntrySlot idx) lastTarget _
            (expirySlot pauser) (pairNe hexpiryIdx.2),
          temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.2),
          temporalSloadBase_getStorVal,
          temporalSstorePost_other _ _ (assignmentSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.1),
          temporalSloadBase_getStorVal]

/-- Exact production-body reserve for unregistering a recorded target that is
not the array's last entry, with the old pauser retained. -/
def foundZeroRetainedSwapPopRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost : Nat) : Nat :=
  221 + foundZeroRetainedSwapPopSetPauserKernelGas sevm base target oldPauser
    assignmentCost countCost holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost

/-- Exact successful production body for unregistering a recorded target that
is **not** the array's last entry (`index + 1 < entries.length`), with the old
pauser retained (`oldCount - 1 ≠ 0`), so `registerAfterSet` stops without
touching any expiry slot. -/
theorem registerPauser_body_foundZeroRetainedSwapPop_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (index + 1))) ∈ base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget,
      indexSlot (sourceLastTarget entries)) ∈ base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + foundZeroRetainedSwapPopRegisterBodyGas sevm base target
            oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  rcases registerMemory_spec target 0 with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      _hpreviousRead, hcontinuationRead⟩
  rcases setPauserKernel_foundZeroRetainedSwapPop_runCompiled dp sevm base
      (registerMemory target 0) (registerImage target 0)
      entries target index oldPauser oldCount assignmentOriginal countOriginal
      holeOriginal movedOriginal tailOriginal lengthOriginal indexOriginal
      assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G
      hw hfind hnotLast hwf hreads htargetRead hnewRead hcontinuationRead
      htargetValid holdValid hsize hassignmentOrig hassignmentCost hcount
      hcountOrig hcountCost hremaining hholeOrig hmovedOrig htailOrig
      hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
      hlengthRestoreCost hindexClearCost hwarmHole hwarmMoved hwarmTail
      hwarmIndex hwarmLength hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hkernel, hgas, hlogs,
      hexpiries⟩
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, hgas, hlogs,
    hexpiries⟩
  have htargetMask := canonicalAddress_mask_zero htargetValid.2
  have hnewMask : addressMask &&& (0 : B256) = 0 := by decide +kernel
  have hbody := registerPauser_body_from_kernel_runCompiled dp sevm base target
    (G + foundZeroRetainedSwapPopSetPauserKernelGas sevm base target oldPauser
      assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost) post hdata hadmin hargTarget hargNew
    htargetMask hnewMask hkernel
  simp only [foundZeroRetainedSwapPopRegisterBodyGas]
  have hg :
      G + (221 + foundZeroRetainedSwapPopSetPauserKernelGas sevm base target
        oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost) =
      (G + foundZeroRetainedSwapPopSetPauserKernelGas sevm base target
        oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost) + 221 := by
    omega
  rw [hg]
  exact hbody

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-runtime success for unregistering a recorded target that is
**not** the array's last entry, with the old pauser retained. -/
theorem registerPauser_runCompiledTo_foundZeroRetainedSwapPop
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (index + 1))) ∈ base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget,
      indexSlot (sourceLastTarget entries)) ∈ base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            foundZeroRetainedSwapPopRegisterBodyGas sevm base target oldPauser
              assignmentCost countCost holeCost movedIndexCost tailClearCost
              lengthRestoreCost indexClearCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      (∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_foundZeroRetainedSwapPop_runCompiled dp sevm base
      entries target index oldPauser oldCount assignmentOriginal countOriginal
      holeOriginal movedOriginal tailOriginal lengthOriginal indexOriginal
      assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G
      hbodyData hadmin hargTarget hargNew hw hfind hnotLast htargetValid
      holdValid hassignmentOrig hassignmentCost hcount hcountOrig hcountCost
      hremaining hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig
      hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
      hindexClearCost hwarmHole hwarmMoved hwarmTail hwarmIndex hwarmLength
      hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hbody, hgas, hlogs,
      hexpiries⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (foundZeroRetainedSwapPopRegisterBodyGas sevm base target oldPauser
        assignmentCost countCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
    hexpiries, hcompile⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact clean direct-message effects for unregistering a recorded target that
is **not** the array's last entry (`index + 1 < entries.length`), with the old
pauser retained (`oldCount - 1 ≠ 0`), derived from the generated-runtime
execution.  This is the general swap-and-pop removal reaching the public
boundary: the last array entry is moved into the removed target's hole and its
reverse index repaired, and no expiry slot moves. -/
theorem registerPauser_foundZeroRetainedSwapPop_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr} {final settled : Devm}
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target 0)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      foundZeroRetainedSwapPopRegisterBodyGas (initSevm msg) (initDevm msg)
        target oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor (initDevm msg) ca)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost (initSevm msg) (initDevm msg)
      target 0).getStorVal ca (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hremaining : oldCount - 1 ≠ 0)
    (hholeOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal (initSevm msg) ca arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (ca, arrayEntrySlot (Nat.toB256 (index + 1))) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmMoved : (ca, indexSlot (sourceLastTarget entries)) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmTail : (ca, arrayEntrySlot (Nat.toB256 entries.length)) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmIndex : (ca, indexSlot target) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmLength : (ca, arrayLengthSlot) ∈
      (initDevm msg).accessedStorageKeys)
    (hgasFinal : gCallStipend < G + 2120 + indexClearCost)
    (hstatic : (initSevm msg).isStatic = false)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    ∃ trace,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor (initDevm msg) ca) trace.writes))
        trace.postEntries ∧
      settled.gasLeft = G ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, oldPauser, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        settled.getStorVal ca (expirySlot pauser) =
          (initDevm msg).getStorVal ca (expirySlot pauser) := by
  have hdataInit : (initSevm msg).data =
      registerPauserCalldata target 0 := by
    simpa [initSevm] using hdata
  rcases registerPauserCalldata_spec (initSevm msg) target 0 hdataInit with
    ⟨hdataLength, hselector, hargTarget, hargNew⟩
  have hvalueInit : (initSevm msg).value = 0 := by
    simpa [initSevm] using hvalue
  have hownerInit : (initSevm msg).currentTarget = ca := by
    simpa [initSevm] using howner
  have hcodeAddressInit : (initSevm msg).codeAddress =
      some (initSevm msg).currentTarget := by
    simpa [initSevm, howner] using hcodeAddress
  have hcodeInit : (initSevm msg).code.toList =
      lidoCircuitBreakerCode dp := by
    simpa [initSevm] using hcode
  have hadminInit : (initSevm msg).caller.toB256 = dp.admin := by
    simpa [initSevm] using hadmin
  rcases registerPauser_runCompiledTo_foundZeroRetainedSwapPop dp (initSevm msg)
      (initDevm msg) entries target index oldPauser oldCount
      assignmentOriginal countOriginal holeOriginal movedOriginal tailOriginal
      lengthOriginal indexOriginal assignmentCost countCost holeCost
      movedIndexCost tailClearCost lengthRestoreCost indexClearCost G
      hdataLength hvalueInit hselector hcodeAddressInit hcodeInit hadminInit
      hargTarget hargNew (by simpa [hownerInit] using hw) hfind hnotLast
      htargetValid holdValid
      (by simpa [hownerInit] using hassignmentOrig) hassignmentCost
      (by simpa [hownerInit] using hcount)
      (by simpa [hownerInit] using hcountOrig) hcountCost hremaining
      (by simpa [hownerInit] using hholeOrig)
      (by simpa [hownerInit] using hmovedOrig)
      (by simpa [hownerInit] using htailOrig)
      (by simpa [hownerInit] using hindexOrig)
      (by simpa [hownerInit] using hlengthOrig) hholeCost hmovedIndexCost
      htailClearCost hlengthRestoreCost hindexClearCost
      (by simpa [hownerInit] using hwarmHole)
      (by simpa [hownerInit] using hwarmMoved)
      (by simpa [hownerInit] using hwarmTail)
      (by simpa [hownerInit] using hwarmIndex)
      (by simpa [hownerInit] using hwarmLength) hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
      hexpiries, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          foundZeroRetainedSwapPopRegisterBodyGas (initSevm msg) (initDevm msg)
            target oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost⟩ =
        initDevm msg := by
    rw [← hgasEntry]
    rfl
  have hrunEntry : Prog.RunCompiledTo (initSevm msg) (initDevm msg)
      (runtime dp) (.ok post) := by
    rw [hentryState] at hrun
    exact hrun
  have hexecEq : exec ⟨0, initSevm msg, initDevm msg⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrunEntry hcompile
  obtain ⟨hpostExec⟩ :=
    (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok post)).mpr
      hexecEq
  change Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hsettledFinal := registerPauser_success_settles_cleanly dp
    htargetOwner howner hcodeAddress hcode hvalue hdata hprocess hclean
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  refine ⟨trace, htrace, hpostEntries, ?_, hgas, ?_, ?_⟩
  · simpa [hownerInit] using hwpost
  · simpa [hownerInit] using hlogs
  · intro pauser hpauser
    simpa [hownerInit] using hexpiries pauser hpauser

/-! ## Found-target zero-pauser registration retiring the old pauser

The third combination of the chronology: the removed target is the array's last
entry, but the old pauser's decremented count reaches zero, so `registerAfterSet`
takes the old-last arm — it clears the old pauser's heartbeat expiry and emits a
zero-payload `HeartbeatUpdated(oldPauser)` before stopping.  The `PauserSet`
record still comes first.  The expiry/event suffix is the same one the
replacement chronology reaches with a nonzero new pauser. -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- `finishSetPauser` for the old-last unregistration arm: the `PauserSet` record
is emitted, then `registerAfterSet` clears the retired pauser's expiry and emits
its zero-payload `HeartbeatUpdated`.  1935 gas of `finishSetPauser` glue above
the 1590 + `clearCost` of `registerAfterSet_oldLastZero_runCompiled`. -/
private theorem finishSetPauser_oldLastZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldPauser oldExpiry oldExpiryOriginal : B256)
    (stack : List B256) (clearCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (holdNonzero : oldPauser ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget (countSlot oldPauser) = 0)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hstatic : sevm.isStatic = false) :
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    let heartbeatLog : Log :=
      ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
        (0 : B256).toBytes⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G + 3525 + clearCost⟩) finishSetPauser
      (((temporalSstorePost sevm (base.addLog eventLog)
        (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
        ⟨stack, M.write 0 (0 : B256).toBytes, G⟩) := by
  dsimp only
  have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
      (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
  have accessedStorageKeys_addLog (d : Devm) (l : Log) :
      (d.addLog l).accessedStorageKeys = d.accessedStorageKeys := rfl
  have hregister := registerAfterSet_oldLastZero_runCompiled
    ((runtime dp).main :: (runtime dp).aux) sevm
    (base.addLog ⟨sevm.currentTarget,
      [pauserSetEvent, target, oldPauser, 0], []⟩)
    M img oldPauser oldExpiry oldExpiryOriginal stack clearCost G hstack hwf
    hreads hprevious hnew holdNonzero
    (by rw [getStorVal_addLog]; exact hcount)
    (by rw [accessedStorageKeys_addLog]; exact hwarmCount)
    (by rw [getStorVal_addLog]; exact hexpiry) hexpiryOrig
    (by rw [accessedStorageKeys_addLog]; exact hwarmExpiry) hclearCost
    hgasStipend hstatic hsize halign
  have h := finishSetPauser_registerAfterSet_runCompiled dp sevm base M img
    target oldPauser 0 stack (G + 1590 + clearCost) _ hstack hreads htarget
    hprevious hnew hcontinuation hsize halign hstatic hregister
  have hg : G + 1590 + clearCost + 1935 = G + 3525 + clearCost := by omega
  rw [hg] at h
  exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The degenerate removal walk at the found-target/zero-pauser leaf with the
old pauser **retired**: its decremented count is already zero, so the removal
walk's `finishSetPauser` continuation clears the old pauser's expiry and emits
the second record.  Both the retired pauser's count and its expiry cell are
carried past all five array-region writes. -/
private theorem removeTarget_foundZeroOldLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next oldPauser oldExpiry oldExpiryOriginal : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost clearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = next)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal next next =
      movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal next 0 = indexClearCost)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hwarmArray : (sevm.currentTarget, arrayEntrySlot next) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : next - 1 = oldLength)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let removePost := indexClearPost sevm
      (entryClearPost sevm base target next) target oldLength
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    let heartbeatLog : Log :=
      ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
        (0 : B256).toBytes⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget
      (((temporalSstorePost sevm (removePost.addLog eventLog)
        (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
        ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩) := by
  dsimp only
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let countKey := countSlot oldPauser
  let expiryKey := expirySlot oldPauser
  let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    target.toBytes
  let tailPost := entryClearPost sevm base target next
  let removePost := indexClearPost sevm tailPost target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let heartbeatLog : Log :=
    ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
      (0 : B256).toBytes⟩
  have hwfIndex : Mem.Wf MIndex := hwf.write _ _
  have hreadsIndex : Mem.Reads MIndex imgIndex :=
    Mem.Reads.write hwf hreads _ _
  have hwfLength : Mem.Wf MLength := hwfIndex.write _ _
  have hreadsLength : Mem.Reads MLength imgLength :=
    Mem.Reads.write hwfIndex hreadsIndex _ _
  have hwfLast : Mem.Wf MLast := hwfLength.write _ _
  have hreadsLast : Mem.Reads MLast imgLast :=
    Mem.Reads.write hwfLength hreadsLength _ _
  have hsizeIndex : MIndex.size = max entrySize 672 := by
    dsimp only [MIndex]
    rw [Mem.size_write_word_at,
      show (removedIndexWord * 32).toNat + 32 = 672 by decide, hsize,
      show ceil32 672 = 672 by decide]
    split <;> omega
  have hsizeLength : MLength.size = 704 := by
    dsimp only [MLength]
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide,
      hsizeIndex, show ceil32 704 = 704 by decide]
    split <;> omega
  have hsizeLast : MLast.size = 736 := by
    dsimp only [MLast]
    rw [Mem.size_write_word_at,
      show (lastTargetWord * 32).toNat + 32 = 736 by decide,
      hsizeLength]
    split
    · omega
    · decide
  have halignIndex : MIndex.size % 32 = 0 :=
    Mem.aligned_write_word halign
  have halignLength : MLength.size % 32 = 0 :=
    Mem.aligned_write_word halignIndex
  have halignLast : MLast.size % 32 = 0 :=
    Mem.aligned_write_word halignLength
  have earlierLast {word : B256}
      (hindexBefore : (word * 32).toNat + 32 ≤
        (removedIndexWord * 32).toNat)
      (hlengthBefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat)
      (hlastBefore : (word * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat) :
      Bytes.toB256 (imgLast.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlastBefore]
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlengthBefore]
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hindexBefore]
  have htargetLast : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target :=
    (earlierLast (by decide) (by decide) (by decide)).trans htarget
  have hpreviousLast : Bytes.toB256
      (imgLast.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser :=
    (earlierLast (by decide) (by decide) (by decide)).trans hprevious
  have hnewLast : Bytes.toB256
      (imgLast.sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hnew
  have hcontinuationLast : Bytes.toB256
      (imgLast.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hcontinuation
  have harrayFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hnextBound
  have hpairs := registryAddressFamilies_pairwise
    htargetValid.2 htargetValid.2 holdValid.2
  have hlengthCount := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have hexpiryArray := expirySlot_ne_arrayFamily holdValid.2 hnextBound
  have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
    holdValid.2 htargetValid.2 holdValid.2
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have transport {key : B256}
      (hindexNe : key ≠ indexKey) (hlengthNe : key ≠ arrayLengthSlot)
      (harrayNe : key ≠ arrayKey) :
      removePost.getStorVal sevm.currentTarget key =
        base.getStorVal sevm.currentTarget key := by
    simp only [removePost, tailPost, indexClearPost,
      lengthWritePost, entryClearPost, indexWritePost, entryWritePost]
    rw [temporalSstorePost_other _ _ (indexSlot target) 0 _ key
        (pairNe hindexNe),
      temporalSstorePost_other _ _ arrayLengthSlot oldLength _ key
        (pairNe hlengthNe),
      temporalSstorePost_other _ _ arrayKey 0 _ key (pairNe harrayNe),
      temporalSstorePost_other _ _ indexKey next _ key (pairNe hindexNe),
      temporalSstorePost_other _ _ arrayKey target _ key (pairNe harrayNe)]
  have hcountRemove : removePost.getStorVal sevm.currentTarget countKey = 0 := by
    rw [transport (Ne.symm hpairs.2.2) hlengthCount.2.2 harrayFamilies.2.2]
    exact hcount
  have hexpiryRemove : removePost.getStorVal sevm.currentTarget expiryKey =
      oldExpiry := by
    rw [transport hexpiryRegistry.2.1 hexpiryArray.1 hexpiryArray.2]
    exact hexpiry
  have hwarmRemove : ∀ key : B256,
      (sevm.currentTarget, key) ∈ base.accessedStorageKeys →
      (sevm.currentTarget, key) ∈ removePost.accessedStorageKeys := by
    intro key hkey
    simp only [removePost, tailPost, indexClearPost,
      lengthWritePost, entryClearPost, indexWritePost, entryWritePost,
      temporalSstorePost_accessedStorageKeys]
    exact hkey
  have hfinish := finishSetPauser_oldLastZero_runCompiled dp sevm removePost
    MLast imgLast target oldPauser oldExpiry oldExpiryOriginal stack clearCost G
    hstack hwfLast hreadsLast htargetLast hpreviousLast hnewLast
    hcontinuationLast holdValid.1
    (by simpa only [countKey] using hcountRemove)
    (hwarmRemove _ hwarmCount)
    (by simpa only [expiryKey] using hexpiryRemove) hexpiryOrig
    (hwarmRemove _ hwarmExpiry) hclearCost hgasStipend
    (by rw [hsizeLast]; decide) halignLast hstatic
  have hrun := removeTarget_toFinish_runCompiled dp sevm base M img
    target oldLength next stack hstack arrayOriginal indexOriginal
    lengthOriginal holeCost movedIndexCost tailClearCost lengthRestoreCost
    indexClearCost (3525 + clearCost) G hwf hreads htarget htargetValid
    hnextNonzero hnextBound entrySize indexExtCost lengthExtCost 4 hsize halign
    hentryLow hindexExtCost hlengthExtCost
    (by rw [Nat.max_eq_right hentryHigh]; decide) harray hindex hlength
    harrayOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
    hlengthRestoreCost hindexClearCost hwarmArray hwarmIndex hwarmLength hsub
    (by omega) hstatic
    (((temporalSstorePost sevm (removePost.addLog eventLog)
      (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
      ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩)
    (by
      dsimp only
      have hg : G + (3525 + clearCost) = G + 3525 + clearCost := by omega
      rw [hg]
      simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog,
        heartbeatLog] using hfinish)
  have hg : G + (3525 + clearCost) + 439 + 4 + indexExtCost + lengthExtCost +
      holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
      indexClearCost =
      G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost := by omega
  rw [hg] at hrun
  simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog,
    heartbeatLog] using hrun

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The `afterOldPauser` glue above the old-last removal walk: the new-pauser
scratch word is zero, so the walk branches straight to `removeTarget` for 35
gas. -/
private theorem afterOldPauser_foundZeroOldLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next oldPauser oldExpiry oldExpiryOriginal : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost clearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = next)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal next next =
      movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal next 0 = indexClearCost)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hwarmArray : (sevm.currentTarget, arrayEntrySlot next) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : next - 1 = oldLength)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let removePost := indexClearPost sevm
      (entryClearPost sevm base target next) target oldLength
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    let heartbeatLog : Log :=
      ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
        (0 : B256).toBytes⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 4003 + clearCost + indexExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      afterOldPauser
      (((temporalSstorePost sevm (removePost.addLog eventLog)
        (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
        ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩) := by
  dsimp only
  let fs := (runtime dp).main :: (runtime dp).aux
  let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let removePost := indexClearPost sevm
    (entryClearPost sevm base target next) target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let heartbeatLog : Log :=
    ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
      (0 : B256).toBytes⟩
  have hremove := removeTarget_foundZeroOldLast_runCompiled dp sevm base M
    img target oldLength next oldPauser oldExpiry oldExpiryOriginal stack
    hstack arrayOriginal indexOriginal lengthOriginal holeCost movedIndexCost
    tailClearCost lengthRestoreCost indexClearCost clearCost G hwf hreads
    htarget hprevious hnew hcontinuation htargetValid holdValid hnextNonzero
    hnextBound entrySize indexExtCost lengthExtCost hsize halign hentryLow
    hentryHigh hindexExtCost hlengthExtCost harray hindex hlength hcount
    hexpiry hexpiryOrig harrayOrig hindexOrig hlengthOrig hholeCost
    hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    hclearCost hwarmArray hwarmIndex hwarmLength hwarmCount hwarmExpiry hsub
    hgasStipend hstatic
  have h := afterOldPauser_removeTarget_runCompiled dp sevm base M img
    stack
    (G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
      movedIndexCost + tailClearCost + lengthRestoreCost + indexClearCost)
    (((temporalSstorePost sevm (removePost.addLog eventLog)
      (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
      ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩)
    hstack hreads hnew (by omega) halign
    (by simpa only [fs, MIndex, MLength, MLast, removePost, eventLog,
      heartbeatLog] using hremove)
  have hg : G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost + indexClearCost +
        35 =
      G + 4003 + clearCost + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost := by omega
  rw [hg] at h
  exact h

/-- Exact reserve for the found-target/zero-pauser kernel when the removed
target is the array's last entry and the old pauser is **retired**: the same
shape as the retained row plus the expiry-clear value cost and the 1417 gas of
the old-last `registerAfterSet` arm. -/
private def foundZeroOldLastSetPauserKernelGas (sevm : Sevm) (base : Devm)
    (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost : Nat) : Nat :=
  4131 + temporalSloadCost sevm base (assignmentSlot target) + assignmentCost +
    temporalSloadCost sevm (assignmentPost sevm base target 0)
      (countSlot oldPauser) + countCost + holeCost + movedIndexCost +
    tailClearCost + lengthRestoreCost + indexClearCost + clearCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-kernel success for unregistering a recorded target that is
already the array's last entry, where the old pauser holds **no** further
assignment afterwards (`oldCount - 1 = 0`).  `registerAfterSet` takes the
old-last arm: it clears the retired pauser's heartbeat expiry and emits a
zero-payload `HeartbeatUpdated(oldPauser)` after the `PauserSet` record, then
stops because the new pauser is zero.

Two records are emitted, in order, and exactly one expiry cell moves — the
retired pauser's, to `0`.  Every other canonical pauser's expiry is preserved. -/
theorem setPauserKernel_foundZeroOldLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (entries : List Entry) (target : B256)
    (index : Nat) (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hsize : M.size = 640)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M,
          G + foundZeroOldLastSetPauserKernelGas sevm base target oldPauser
            assignmentCost countCost holeCost movedIndexCost tailClearCost
            lengthRestoreCost indexClearCost clearCost⟩)
        setPauserKernel post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
           (0 : B256).toBytes⟩] ∧
      post.getStorVal sevm.currentTarget (expirySlot oldPauser) = 0 ∧
      ∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
      (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
  have expirySlotNe {left right : B256} (hleft : canonicalAddress left)
      (hright : canonicalAddress right) (hne : left ≠ right) :
      expirySlot left ≠ expirySlot right := by
    intro hslot
    exact hne (addressSlot_injective (region := expiryRegion)
      (by norm_num [expiryRegion]) hleft hright
      (by simpa only [expirySlot] using hslot))
  have hindexLt : index < entries.length := findEntry_index_lt hfind
  let next : B256 := Nat.toB256 entries.length
  let oldLength : B256 := next - 1
  let assignPost := assignmentPost sevm base target 0
  let countBase := temporalSloadBase sevm assignPost (countSlot oldPauser)
  let countPost := temporalSstorePost sevm countBase (countSlot oldPauser)
    (oldCount - 1)
  let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    oldPauser.toBytes
  have hlength256 := hw.entries_length_lt_2pow256
  have hnextBound : next.toNat < 2 ^ 252 := by
    dsimp only [next]
    rw [B256.toNat_toB256_of_lt hlength256]
    exact hw.entries_length_lt_2pow252
  have hnextNonzero : next ≠ 0 := by
    intro hz
    have h := congrArg B256.toNat hz
    rw [show next = Nat.toB256 entries.length from rfl,
      B256.toNat_toB256_of_lt hlength256] at h
    simp only [B256.toNat_zero] at h
    omega
  have hstorAssignment : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = oldPauser := by
    change (Devm.getStor base sevm.currentTarget).get (assignmentSlot target) =
      oldPauser
    simpa [logicalStorageOfStor, findEntry_assignmentAt hfind] using
      hw.assignments target htargetValid.2
  have hstorArray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target := by
    have h := hw.arrayWords index hindexLt
    rw [findEntry_targetAt hfind, hlast] at h
    change (Devm.getStor base sevm.currentTarget).get
      (arrayEntrySlot next) = target
    simpa [logicalStorageOfStor, next] using h
  have hstorIndex : base.getStorVal sevm.currentTarget (indexSlot target) =
      next := by
    have h := hw.indices target htargetValid.2
    rw [findEntry_oneBasedIndexAt hfind, hlast] at h
    change (Devm.getStor base sevm.currentTarget).get (indexSlot target) = next
    simpa [logicalStorageOfStor, next] using h
  have hstorLength : base.getStorVal sevm.currentTarget arrayLengthSlot =
      next := by
    change (Devm.getStor base sevm.currentTarget).get arrayLengthSlot = next
    simpa [logicalStorageOfStor, next] using hw.lengthWord
  have hpairwise := registryAddressFamilies_pairwise htargetValid.2
    htargetValid.2 holdValid.2
  have hentryNe := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hnextBound
  have hlengthNe := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have hexpiryOldRegistry := expirySlot_ne_registryAddressFamilies
    holdValid.2 htargetValid.2 holdValid.2
  have hexpiryOldArray := expirySlot_ne_arrayFamily holdValid.2 hnextBound
  have htransport : ∀ k : B256, k ≠ countSlot oldPauser →
      k ≠ assignmentSlot target →
      countPost.getStorVal sevm.currentTarget k =
        base.getStorVal sevm.currentTarget k := by
    intro k hcountNe hassignNe
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _ k
        (pairNe hcountNe),
      temporalSloadBase_getStorVal,
      temporalSstorePost_other _ _ (assignmentSlot target) 0 _ k
        (pairNe hassignNe),
      temporalSloadBase_getStorVal]
  have harray : countPost.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target := by
    rw [htransport _ (Ne.symm hentryNe.2.2) (Ne.symm hentryNe.1)]
    exact hstorArray
  have hindexVal : countPost.getStorVal sevm.currentTarget
      (indexSlot target) = next := by
    rw [htransport _ hpairwise.2.2 (Ne.symm hpairwise.1)]
    exact hstorIndex
  have hlengthVal : countPost.getStorVal sevm.currentTarget arrayLengthSlot =
      next := by
    rw [htransport _ (Ne.symm hlengthNe.2.2) (Ne.symm hlengthNe.1)]
    exact hstorLength
  have hexpiryVal : countPost.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry := by
    rw [htransport _ hexpiryOldRegistry.2.2 hexpiryOldRegistry.1]
    exact hexpiry
  have hcountVal : countPost.getStorVal sevm.currentTarget
      (countSlot oldPauser) = 0 := by
    dsimp only [countPost]
    rw [temporalSstorePost_self _ _ _ _]
    exact hretired
  have hwarmTransport : ∀ k : B256,
      (sevm.currentTarget, k) ∈ base.accessedStorageKeys →
      (sevm.currentTarget, k) ∈ countPost.accessedStorageKeys := by
    intro k hk
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_accessedStorageKeys]
    refine temporalSloadBase_preserves_warm _ _ _ _ ?_
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm _ _ _ _ hk
  have hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      countPost.accessedStorageKeys := by
    dsimp only [countPost]
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_warm _ _ _
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          rw [hsize]
          decide))
  have hsize' : M'.size = 640 := by rw [hsizeM', hsize]
  have htarget' : Bytes.toB256
      (img'.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hprevious' : Bytes.toB256
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser := by
    dsimp only [img']
    rw [show 32 = oldPauser.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hcontinuation' : Bytes.toB256
      (img'.sliceD (continuationWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      decide)]
    exact hcontinuation
  let MIndex := M'.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let removePost := indexClearPost sevm
    (entryClearPost sevm countPost target next) target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let heartbeatLog : Log :=
    ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
      (0 : B256).toBytes⟩
  let post := ((temporalSstorePost sevm (removePost.addLog eventLog)
    (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
      ⟨[], MLast.write 0 (0 : B256).toBytes, G⟩
  have hafterRun := afterOldPauser_foundZeroOldLast_runCompiled dp sevm
    countPost M' img' target oldLength next oldPauser oldExpiry
    oldExpiryOriginal [] (by simp) arrayOriginal indexOriginal lengthOriginal
    holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost
    clearCost G hwf' hreads' htarget' hprevious' hnew' hcontinuation'
    htargetValid holdValid hnextNonzero hnextBound 640 3 3 hsize'
    (by rw [hsize']) (by decide) (by decide) (by decide) (by decide)
    harray hindexVal hlengthVal hcountVal hexpiryVal hexpiryOrig harrayOrig
    hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
    hlengthRestoreCost hindexClearCost hclearCost
    (hwarmTransport _ hwarmArray) (hwarmTransport _ hwarmIndex)
    (hwarmTransport _ hwarmLength) hwarmCount (hwarmTransport _ hwarmExpiry)
    rfl hgasStipend hstatic
  dsimp only at hafterRun
  have hgAfter : G + 4003 + clearCost + 3 + 3 + holeCost + movedIndexCost +
      tailClearCost + lengthRestoreCost + indexClearCost =
      G + (4009 + clearCost + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost) := by omega
  rw [hgAfter] at hafterRun
  have hkernel := setPauserKernel_found_runCompiled dp sevm base M img post
    target 0 oldPauser oldCount assignmentOriginal countOriginal
    assignmentCost countCost
    (4009 + clearCost + holeCost + movedIndexCost + tailClearCost +
      lengthRestoreCost + indexClearCost) G
    hwf hreads htarget hnew htargetValid holdValid hsize.symm.le
    (by rw [hsize]) hstorAssignment
    hassignmentOrig hassignmentCost hcount hcountOrig hcountCost
    (by omega) hstatic
    (by
      simpa only [countPost, countBase, assignPost, M', MIndex, MLength,
        MLast, removePost, eventLog, heartbeatLog, post] using hafterRun)
  have hsetPauser : setPauser entries target 0 =
      some (swapPop entries index) := by
    simp [setPauser, htargetValid.1, hfind]
  obtain ⟨trace, htrace⟩ : ∃ trace,
      setPauserSourceTrace entries target 0 = some trace := by
    simp [setPauserSourceTrace, hsetPauser]
  have hrefines := setPauser_sourceTrace_refines_model htargetValid.1 htrace
  have hpostEntries : trace.postEntries = swapPop entries index := by
    rw [hsetPauser] at hrefines
    exact (Option.some.inj hrefines.1).symm
  have hwpost := hw.applySetPauserSourceTrace htargetValid.2 hzeroCanonical
    htrace
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, rfl, ?_, ?_, ?_⟩
  · have hgTotal : G + foundZeroOldLastSetPauserKernelGas sevm base target
          oldPauser assignmentCost countCost holeCost movedIndexCost
          tailClearCost lengthRestoreCost indexClearCost clearCost =
        G + (4009 + clearCost + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) +
          foundSetPauserKernelPrefixGas sevm base target 0 oldPauser
            assignmentCost countCost := by
      dsimp only [foundZeroOldLastSetPauserKernelGas,
        foundSetPauserKernelPrefixGas]
      omega
    rw [hgTotal]
    exact hkernel
  · have logs_setMach (d : Devm) (mach : Mach) :
        (d.setMach mach).logs = d.logs := rfl
    have logs_addLog (d : Devm) (log : Log) :
        (d.addLog log).logs = d.logs ++ [log] := rfl
    dsimp only [post, removePost, countPost, countBase, assignPost,
      assignmentPost, assignmentBase, eventLog, heartbeatLog]
    rw [logs_setMach, logs_addLog, temporalSstorePost_logs, logs_addLog]
    simp only [indexClearPost, lengthWritePost,
      entryClearPost, indexWritePost, entryWritePost,
      temporalSstorePost_logs, temporalSloadBase_logs, List.append_assoc,
      List.cons_append, List.nil_append]
  · dsimp only [post]
    rw [Devm.getStorVal_setMach, getStorVal_addLog]
    exact temporalSstorePost_self _ _ _ _
  · intro pauser hpauser hne
    have hexpiryArray := expirySlot_ne_arrayFamily hpauser hnextBound
    have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
      hpauser htargetValid.2 holdValid.2
    have hexpiryOther : expirySlot pauser ≠ expirySlot oldPauser :=
      expirySlotNe hpauser holdValid.2 hne
    calc
      post.getStorVal sevm.currentTarget (expirySlot pauser) =
          (temporalSstorePost sevm (removePost.addLog eventLog)
            (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
              (expirySlot pauser) := by
        dsimp only [post]
        rw [Devm.getStorVal_setMach, getStorVal_addLog]
      _ = base.getStorVal sevm.currentTarget (expirySlot pauser) := by
        rw [temporalSstorePost_other _ _ (expirySlot oldPauser) 0 _
            (expirySlot pauser) (pairNe hexpiryOther),
          getStorVal_addLog]
        dsimp only [removePost, countPost, countBase, assignPost,
          assignmentPost, assignmentBase]
        simp only [indexClearPost, lengthWritePost,
          entryClearPost, indexWritePost, entryWritePost]
        rw [temporalSstorePost_other _ _ (indexSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.1),
          temporalSstorePost_other _ _ arrayLengthSlot oldLength _
            (expirySlot pauser) (pairNe hexpiryArray.1),
          temporalSstorePost_other _ _ (arrayEntrySlot next) 0 _
            (expirySlot pauser) (pairNe hexpiryArray.2),
          temporalSstorePost_other _ _ (indexSlot target) next _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.1),
          temporalSstorePost_other _ _ (arrayEntrySlot next) target _
            (expirySlot pauser) (pairNe hexpiryArray.2),
          temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.2),
          temporalSloadBase_getStorVal,
          temporalSstorePost_other _ _ (assignmentSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.1),
          temporalSloadBase_getStorVal]

/-- Exact production-body reserve for unregistering a recorded target that is
already the array's last entry, retiring the old pauser. -/
def foundZeroOldLastRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost : Nat) : Nat :=
  221 + foundZeroOldLastSetPauserKernelGas sevm base target oldPauser
    assignmentCost countCost holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost clearCost

/-- Exact successful production body for unregistering a recorded target that is
already the array's last entry (`index + 1 = entries.length`) and retires the old
pauser (`oldCount - 1 = 0`). -/
theorem registerPauser_body_foundZeroOldLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + foundZeroOldLastRegisterBodyGas sevm base target oldPauser
            assignmentCost countCost holeCost movedIndexCost tailClearCost
            lengthRestoreCost indexClearCost clearCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
           (0 : B256).toBytes⟩] ∧
      post.getStorVal sevm.currentTarget (expirySlot oldPauser) = 0 ∧
      ∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  rcases registerMemory_spec target 0 with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      _hpreviousRead, hcontinuationRead⟩
  rcases setPauserKernel_foundZeroOldLast_runCompiled dp sevm base
      (registerMemory target 0) (registerImage target 0)
      entries target index oldPauser oldCount oldExpiry oldExpiryOriginal
      assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal assignmentCost countCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost clearCost G
      hw hfind hlast hwf hreads htargetRead hnewRead hcontinuationRead
      htargetValid holdValid hsize hassignmentOrig hassignmentCost hcount
      hcountOrig hcountCost hretired hexpiry hexpiryOrig hclearCost harrayOrig
      hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
      hlengthRestoreCost hindexClearCost hwarmArray hwarmIndex hwarmLength
      hwarmExpiry hgasStipend hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hkernel, hgas, hlogs,
      holdExpiryPost, hexpiries⟩
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, hgas, hlogs,
    holdExpiryPost, hexpiries⟩
  have htargetMask := canonicalAddress_mask_zero htargetValid.2
  have hnewMask : addressMask &&& (0 : B256) = 0 := by decide +kernel
  have hbody := registerPauser_body_from_kernel_runCompiled dp sevm base target
    (G + foundZeroOldLastSetPauserKernelGas sevm base target oldPauser
      assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost) post hdata hadmin hargTarget
    hargNew htargetMask hnewMask hkernel
  simp only [foundZeroOldLastRegisterBodyGas]
  have hg :
      G + (221 + foundZeroOldLastSetPauserKernelGas sevm base target oldPauser
        assignmentCost countCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost clearCost) =
      (G + foundZeroOldLastSetPauserKernelGas sevm base target oldPauser
        assignmentCost countCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost clearCost) + 221 := by
    omega
  rw [hg]
  exact hbody

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-runtime success for unregistering a recorded target that is
already the array's last entry, retiring the old pauser. -/
theorem registerPauser_runCompiledTo_foundZeroOldLast
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            foundZeroOldLastRegisterBodyGas sevm base target oldPauser
              assignmentCost countCost holeCost movedIndexCost tailClearCost
              lengthRestoreCost indexClearCost clearCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
           (0 : B256).toBytes⟩] ∧
      post.getStorVal sevm.currentTarget (expirySlot oldPauser) = 0 ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_foundZeroOldLast_runCompiled dp sevm base
      entries target index oldPauser oldCount oldExpiry oldExpiryOriginal
      assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal assignmentCost countCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost clearCost G
      hbodyData hadmin hargTarget hargNew hw hfind hlast htargetValid holdValid
      hassignmentOrig hassignmentCost hcount hcountOrig hcountCost hretired
      hexpiry hexpiryOrig hclearCost harrayOrig hindexOrig hlengthOrig
      hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
      hindexClearCost hwarmArray hwarmIndex hwarmLength hwarmExpiry
      hgasStipend hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hbody, hgas, hlogs,
      holdExpiryPost, hexpiries⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (foundZeroOldLastRegisterBodyGas sevm base target oldPauser
        assignmentCost countCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost clearCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
    holdExpiryPost, hexpiries, hcompile⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact clean direct-message effects for unregistering a recorded target that
is already the array's last entry (`index + 1 = entries.length`) and retires the
old pauser (`oldCount - 1 = 0`), derived from the generated-runtime execution.

Two records are emitted, in order: `PauserSet(target, oldPauser, 0)` and a
zero-payload `HeartbeatUpdated(oldPauser)`.  The retired pauser's expiry cell is
`0` in the settled state and every other canonical pauser's expiry is
unchanged — the observable difference from the retained partition. -/
theorem registerPauser_foundZeroOldLast_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr} {final settled : Devm}
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal arrayOriginal indexOriginal
      lengthOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target 0)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      foundZeroOldLastRegisterBodyGas (initSevm msg) (initDevm msg)
        target oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost clearCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor (initDevm msg) ca)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hlast : index + 1 = entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost (initSevm msg) (initDevm msg)
      target 0).getStorVal ca (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : (initDevm msg).getStorVal ca
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal (initSevm msg) ca
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (harrayOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 entries.length)) = arrayOriginal)
    (hindexOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal (initSevm msg) ca arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length) =
        movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 entries.length) 0 = indexClearCost)
    (hwarmArray : (ca, arrayEntrySlot (Nat.toB256 entries.length)) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmIndex : (ca, indexSlot target) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmLength : (ca, arrayLengthSlot) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmExpiry : (ca, expirySlot oldPauser) ∈
      (initDevm msg).accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : (initSevm msg).isStatic = false)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    ∃ trace,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor (initDevm msg) ca) trace.writes))
        trace.postEntries ∧
      settled.gasLeft = G ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨ca, [heartbeatUpdatedEvent, oldPauser], (0 : B256).toBytes⟩] ∧
      settled.getStorVal ca (expirySlot oldPauser) = 0 ∧
      ∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        settled.getStorVal ca (expirySlot pauser) =
          (initDevm msg).getStorVal ca (expirySlot pauser) := by
  have hdataInit : (initSevm msg).data =
      registerPauserCalldata target 0 := by
    simpa [initSevm] using hdata
  rcases registerPauserCalldata_spec (initSevm msg) target 0 hdataInit with
    ⟨hdataLength, hselector, hargTarget, hargNew⟩
  have hvalueInit : (initSevm msg).value = 0 := by
    simpa [initSevm] using hvalue
  have hownerInit : (initSevm msg).currentTarget = ca := by
    simpa [initSevm] using howner
  have hcodeAddressInit : (initSevm msg).codeAddress =
      some (initSevm msg).currentTarget := by
    simpa [initSevm, howner] using hcodeAddress
  have hcodeInit : (initSevm msg).code.toList =
      lidoCircuitBreakerCode dp := by
    simpa [initSevm] using hcode
  have hadminInit : (initSevm msg).caller.toB256 = dp.admin := by
    simpa [initSevm] using hadmin
  rcases registerPauser_runCompiledTo_foundZeroOldLast dp (initSevm msg)
      (initDevm msg) entries target index oldPauser oldCount oldExpiry
      oldExpiryOriginal assignmentOriginal countOriginal arrayOriginal
      indexOriginal lengthOriginal assignmentCost countCost holeCost
      movedIndexCost tailClearCost lengthRestoreCost indexClearCost clearCost
      G hdataLength hvalueInit hselector hcodeAddressInit hcodeInit hadminInit
      hargTarget hargNew (by simpa [hownerInit] using hw) hfind hlast
      htargetValid holdValid
      (by simpa [hownerInit] using hassignmentOrig) hassignmentCost
      (by simpa [hownerInit] using hcount)
      (by simpa [hownerInit] using hcountOrig) hcountCost hretired
      (by simpa [hownerInit] using hexpiry)
      (by simpa [hownerInit] using hexpiryOrig) hclearCost
      (by simpa [hownerInit] using harrayOrig)
      (by simpa [hownerInit] using hindexOrig)
      (by simpa [hownerInit] using hlengthOrig) hholeCost hmovedIndexCost
      htailClearCost hlengthRestoreCost hindexClearCost
      (by simpa [hownerInit] using hwarmArray)
      (by simpa [hownerInit] using hwarmIndex)
      (by simpa [hownerInit] using hwarmLength)
      (by simpa [hownerInit] using hwarmExpiry) hgasStipend hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
      holdExpiryPost, hexpiries, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          foundZeroOldLastRegisterBodyGas (initSevm msg) (initDevm msg)
            target oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost clearCost⟩ =
        initDevm msg := by
    rw [← hgasEntry]
    rfl
  have hrunEntry : Prog.RunCompiledTo (initSevm msg) (initDevm msg)
      (runtime dp) (.ok post) := by
    rw [hentryState] at hrun
    exact hrun
  have hexecEq : exec ⟨0, initSevm msg, initDevm msg⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrunEntry hcompile
  obtain ⟨hpostExec⟩ :=
    (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok post)).mpr
      hexecEq
  change Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hsettledFinal := registerPauser_success_settles_cleanly dp
    htargetOwner howner hcodeAddress hcode hvalue hdata hprocess hclean
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  refine ⟨trace, htrace, hpostEntries, ?_, hgas, ?_, ?_, ?_⟩
  · simpa [hownerInit] using hwpost
  · simpa [hownerInit] using hlogs
  · simpa [hownerInit] using holdExpiryPost
  · intro pauser hpauser hne
    simpa [hownerInit] using hexpiries pauser hpauser hne

/-! ## Found-target zero-pauser registration retiring the old pauser and
removing an interior entry

The fourth and last combination of the chronology: both restrictions are
lifted at once.  The removed target is not the array's last entry, so the
general swap-and-pop walk runs, and the old pauser's decremented count reaches
zero, so `registerAfterSet` clears its expiry and emits the second record. -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The general swap-and-pop removal walk with the old pauser **retired**: both
the retired pauser's count and its expiry cell are carried past all five
array-region writes, and the removal walk's `finishSetPauser` continuation
clears the expiry and emits the second record. -/
private theorem removeTarget_swapPop_foundZeroOldLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength oldPauser oldExpiry
      oldExpiryOriginal : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost clearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hlastValid : canonicalAddress lastTarget)
    (hlastNe : lastTarget ≠ target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hidxNonzero : idx ≠ 0) (hidxBound : idx.toNat < 2 ^ 252)
    (hlenNonzero : len ≠ 0) (hlenBound : len.toNat < 2 ^ 252)
    (hidxNeLen : idx ≠ len)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (hhole : base.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = holeCurrent)
    (hmoved : base.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = movedCurrent)
    (htail : base.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget)
    (hindex : base.getStorVal sevm.currentTarget (indexSlot target) = idx)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = len)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot idx) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot lastTarget) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot len) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal holeCurrent lastTarget =
      holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal movedCurrent idx =
      movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal lastTarget 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal len oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal idx 0 = indexClearCost)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hwarmHole : (sevm.currentTarget, arrayEntrySlot idx) ∈
      base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget, indexSlot lastTarget) ∈
      base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget, arrayEntrySlot len) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : len - 1 = oldLength)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
    let removePost := indexClearPost sevm
      (swapPopClearPost sevm base lastTarget idx len) target oldLength
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    let heartbeatLog : Log :=
      ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
        (0 : B256).toBytes⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget
      (((temporalSstorePost sevm (removePost.addLog eventLog)
        (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
        ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩) := by
  dsimp only
  let countKey := countSlot oldPauser
  let expiryKey := expirySlot oldPauser
  let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    lastTarget.toBytes
  let tailPost := swapPopClearPost sevm base lastTarget idx len
  let removePost := indexClearPost sevm tailPost target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let heartbeatLog : Log :=
    ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
      (0 : B256).toBytes⟩
  have hwfIndex : Mem.Wf MIndex := hwf.write _ _
  have hreadsIndex : Mem.Reads MIndex imgIndex :=
    Mem.Reads.write hwf hreads _ _
  have hwfLength : Mem.Wf MLength := hwfIndex.write _ _
  have hreadsLength : Mem.Reads MLength imgLength :=
    Mem.Reads.write hwfIndex hreadsIndex _ _
  have hwfLast : Mem.Wf MLast := hwfLength.write _ _
  have hreadsLast : Mem.Reads MLast imgLast :=
    Mem.Reads.write hwfLength hreadsLength _ _
  have hsizeIndex : MIndex.size = max entrySize 672 := by
    dsimp only [MIndex]
    rw [Mem.size_write_word_at,
      show (removedIndexWord * 32).toNat + 32 = 672 by decide, hsize,
      show ceil32 672 = 672 by decide]
    split <;> omega
  have hsizeLength : MLength.size = 704 := by
    dsimp only [MLength]
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide,
      hsizeIndex, show ceil32 704 = 704 by decide]
    split <;> omega
  have hsizeLast : MLast.size = 736 := by
    dsimp only [MLast]
    rw [Mem.size_write_word_at,
      show (lastTargetWord * 32).toNat + 32 = 736 by decide,
      hsizeLength]
    split
    · omega
    · decide
  have halignIndex : MIndex.size % 32 = 0 :=
    Mem.aligned_write_word halign
  have halignLength : MLength.size % 32 = 0 :=
    Mem.aligned_write_word halignIndex
  have halignLast : MLast.size % 32 = 0 :=
    Mem.aligned_write_word halignLength
  have earlierLast {word : B256}
      (hindexBefore : (word * 32).toNat + 32 ≤
        (removedIndexWord * 32).toNat)
      (hlengthBefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat)
      (hlastBefore : (word * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat) :
      Bytes.toB256 (imgLast.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlastBefore]
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlengthBefore]
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hindexBefore]
  have htargetLast : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target :=
    (earlierLast (by decide) (by decide) (by decide)).trans htarget
  have hpreviousLast : Bytes.toB256
      (imgLast.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser :=
    (earlierLast (by decide) (by decide) (by decide)).trans hprevious
  have hnewLast : Bytes.toB256
      (imgLast.sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hnew
  have hcontinuationLast : Bytes.toB256
      (imgLast.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hcontinuation
  have hidxFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hidxBound
  have hlenFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hlenBound
  have hpairs := registryAddressFamilies_pairwise
    htargetValid.2 htargetValid.2 holdValid.2
  have hlastPairs := registryAddressFamilies_pairwise
    htargetValid.2 hlastValid holdValid.2
  have hlengthCount := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have hexpiryIdx := expirySlot_ne_arrayFamily holdValid.2 hidxBound
  have hexpiryLen := expirySlot_ne_arrayFamily holdValid.2 hlenBound
  have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
    holdValid.2 htargetValid.2 holdValid.2
  have hexpiryLastRegistry := expirySlot_ne_registryAddressFamilies
    holdValid.2 hlastValid holdValid.2
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have transport {key : B256}
      (hindexNe : key ≠ indexSlot target)
      (hlengthNe : key ≠ arrayLengthSlot)
      (htailNe : key ≠ arrayEntrySlot len)
      (hmovedNe : key ≠ indexSlot lastTarget)
      (hholeNe : key ≠ arrayEntrySlot idx) :
      removePost.getStorVal sevm.currentTarget key =
        base.getStorVal sevm.currentTarget key := by
    simp only [removePost, tailPost, indexClearPost, lengthWritePost,
      swapPopClearPost, indexWritePost, entryWritePost]
    rw [temporalSstorePost_other _ _ (indexSlot target) 0 _ key
        (pairNe hindexNe),
      temporalSstorePost_other _ _ arrayLengthSlot oldLength _ key
        (pairNe hlengthNe),
      temporalSstorePost_other _ _ (arrayEntrySlot len) 0 _ key
        (pairNe htailNe),
      temporalSstorePost_other _ _ (indexSlot lastTarget) idx _ key
        (pairNe hmovedNe),
      temporalSstorePost_other _ _ (arrayEntrySlot idx) lastTarget _ key
        (pairNe hholeNe)]
  have hcountRemove : removePost.getStorVal sevm.currentTarget countKey = 0 := by
    rw [transport (Ne.symm hpairs.2.2) hlengthCount.2.2 hlenFamilies.2.2
      (Ne.symm hlastPairs.2.2) hidxFamilies.2.2]
    exact hcount
  have hexpiryRemove : removePost.getStorVal sevm.currentTarget expiryKey =
      oldExpiry := by
    rw [transport hexpiryRegistry.2.1 hexpiryLen.1 hexpiryLen.2
      hexpiryLastRegistry.2.1 hexpiryIdx.2]
    exact hexpiry
  have hwarmRemove : ∀ key : B256,
      (sevm.currentTarget, key) ∈ base.accessedStorageKeys →
      (sevm.currentTarget, key) ∈ removePost.accessedStorageKeys := by
    intro key hkey
    simp only [removePost, tailPost, indexClearPost, lengthWritePost,
      swapPopClearPost, indexWritePost, entryWritePost,
      temporalSstorePost_accessedStorageKeys]
    exact hkey
  have hfinish := finishSetPauser_oldLastZero_runCompiled dp sevm removePost
    MLast imgLast target oldPauser oldExpiry oldExpiryOriginal stack clearCost G
    hstack hwfLast hreadsLast htargetLast hpreviousLast hnewLast
    hcontinuationLast holdValid.1
    (by simpa only [countKey] using hcountRemove)
    (hwarmRemove _ hwarmCount)
    (by simpa only [expiryKey] using hexpiryRemove) hexpiryOrig
    (hwarmRemove _ hwarmExpiry) hclearCost hgasStipend
    (by rw [hsizeLast]; decide) halignLast hstatic
  have hrun := removeTarget_swapPop_toFinish_runCompiled dp sevm base M img
    target lastTarget idx len oldLength stack hstack holeCurrent movedCurrent
    holeOriginal movedOriginal tailOriginal lengthOriginal indexOriginal
    holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost
    (3525 + clearCost) G hwf hreads htarget htargetValid hlastValid hlastNe
    hidxNonzero hidxBound hlenNonzero hlenBound hidxNeLen entrySize
    indexExtCost lengthExtCost 4 hsize halign hentryLow hindexExtCost
    hlengthExtCost (by rw [Nat.max_eq_right hentryHigh]; decide)
    hhole hmoved htail hindex hlength hholeOrig hmovedOrig
    htailOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
    hlengthRestoreCost hindexClearCost hwarmHole hwarmMoved hwarmTail
    hwarmIndex hwarmLength hsub (by omega) hstatic
    (((temporalSstorePost sevm (removePost.addLog eventLog)
      (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
      ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩)
    (by
      dsimp only
      have hg : G + (3525 + clearCost) = G + 3525 + clearCost := by omega
      rw [hg]
      simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog,
        heartbeatLog] using hfinish)
  have hg : G + (3525 + clearCost) + 439 + 4 + indexExtCost + lengthExtCost +
      holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
      indexClearCost =
      G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost := by omega
  rw [hg] at hrun
  simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog,
    heartbeatLog] using hrun

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The `afterOldPauser` glue above the general swap-and-pop removal walk that
retires the old pauser: 35 gas for the zero new-pauser branch. -/
private theorem afterOldPauser_swapPop_foundZeroOldLast_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength oldPauser oldExpiry
      oldExpiryOriginal : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost clearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hlastValid : canonicalAddress lastTarget)
    (hlastNe : lastTarget ≠ target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hidxNonzero : idx ≠ 0) (hidxBound : idx.toNat < 2 ^ 252)
    (hlenNonzero : len ≠ 0) (hlenBound : len.toNat < 2 ^ 252)
    (hidxNeLen : idx ≠ len)
    (entrySize indexExtCost lengthExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize) (hentryHigh : entrySize ≤ 704)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (hhole : base.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = holeCurrent)
    (hmoved : base.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = movedCurrent)
    (htail : base.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget)
    (hindex : base.getStorVal sevm.currentTarget (indexSlot target) = idx)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = len)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot idx) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot lastTarget) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot len) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal holeCurrent lastTarget =
      holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal movedCurrent idx =
      movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal lastTarget 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal len oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal idx 0 = indexClearCost)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hwarmHole : (sevm.currentTarget, arrayEntrySlot idx) ∈
      base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget, indexSlot lastTarget) ∈
      base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget, arrayEntrySlot len) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsub : len - 1 = oldLength)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
    let removePost := indexClearPost sevm
      (swapPopClearPost sevm base lastTarget idx len) target oldLength
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
    let heartbeatLog : Log :=
      ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
        (0 : B256).toBytes⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 4003 + clearCost + indexExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      afterOldPauser
      (((temporalSstorePost sevm (removePost.addLog eventLog)
        (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
        ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩) := by
  dsimp only
  let fs := (runtime dp).main :: (runtime dp).aux
  let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let removePost := indexClearPost sevm
    (swapPopClearPost sevm base lastTarget idx len) target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let heartbeatLog : Log :=
    ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
      (0 : B256).toBytes⟩
  have hremove := removeTarget_swapPop_foundZeroOldLast_runCompiled dp sevm
    base M img target lastTarget idx len oldLength oldPauser oldExpiry
    oldExpiryOriginal stack hstack holeCurrent movedCurrent holeOriginal
    movedOriginal tailOriginal lengthOriginal indexOriginal holeCost
    movedIndexCost tailClearCost lengthRestoreCost indexClearCost clearCost G
    hwf hreads htarget hprevious hnew hcontinuation htargetValid hlastValid
    hlastNe holdValid hidxNonzero hidxBound hlenNonzero hlenBound hidxNeLen
    entrySize indexExtCost lengthExtCost hsize halign hentryLow hentryHigh
    hindexExtCost hlengthExtCost hhole hmoved htail hindex hlength hcount
    hexpiry hexpiryOrig hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig
    hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
    hindexClearCost hclearCost hwarmHole hwarmMoved hwarmTail hwarmIndex
    hwarmLength hwarmCount hwarmExpiry hsub hgasStipend hstatic
  have h := afterOldPauser_removeTarget_runCompiled dp sevm base M img
    stack
    (G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
      movedIndexCost + tailClearCost + lengthRestoreCost + indexClearCost)
    (((temporalSstorePost sevm (removePost.addLog eventLog)
      (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
      ⟨stack, MLast.write 0 (0 : B256).toBytes, G⟩)
    hstack hreads hnew (by omega) halign
    (by simpa only [fs, MIndex, MLength, MLast, removePost, eventLog,
      heartbeatLog] using hremove)
  have hg : G + 3968 + clearCost + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost + indexClearCost +
        35 =
      G + 4003 + clearCost + indexExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost := by omega
  rw [hg] at h
  exact h

/-- Exact reserve for the found-target/zero-pauser kernel when the removed
target is not the array's last entry and the old pauser is retired.  Same
constant as the degenerate old-last row: the general swap-and-pop walk costs
the same 443 gas above `finishSetPauser`, and only the five SSTORE value-cost
partitions differ. -/
private def foundZeroOldLastSwapPopSetPauserKernelGas (sevm : Sevm)
    (base : Devm) (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost : Nat) : Nat :=
  4131 + temporalSloadCost sevm base (assignmentSlot target) + assignmentCost +
    temporalSloadCost sevm (assignmentPost sevm base target 0)
      (countSlot oldPauser) + countCost + holeCost + movedIndexCost +
    tailClearCost + lengthRestoreCost + indexClearCost + clearCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-kernel success for the last combination of the chronology:
the removed target is **not** the array's last entry, so the general
swap-and-pop walk moves `sourceLastTarget entries` into the hole at `index + 1`
and repairs its reverse index, and the old pauser is **retired**, so
`registerAfterSet` clears its heartbeat expiry and emits a zero-payload
`HeartbeatUpdated(oldPauser)` after the `PauserSet` record. -/
theorem setPauserKernel_foundZeroOldLastSwapPop_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (entries : List Entry) (target : B256)
    (index : Nat) (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hsize : M.size = 640)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (index + 1))) ∈ base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget,
      indexSlot (sourceLastTarget entries)) ∈ base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M,
          G + foundZeroOldLastSwapPopSetPauserKernelGas sevm base target
            oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost clearCost⟩)
        setPauserKernel post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
           (0 : B256).toBytes⟩] ∧
      post.getStorVal sevm.currentTarget (expirySlot oldPauser) = 0 ∧
      ∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
      (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
  have expirySlotNe {left right : B256} (hleft : canonicalAddress left)
      (hright : canonicalAddress right) (hne : left ≠ right) :
      expirySlot left ≠ expirySlot right := by
    intro hslot
    exact hne (addressSlot_injective (region := expiryRegion)
      (by norm_num [expiryRegion]) hleft hright
      (by simpa only [expirySlot] using hslot))
  have hindexLt : index < entries.length := findEntry_index_lt hfind
  obtain ⟨lastEntry, hlast⟩ := last_some_of_findEntry hfind
  have hlastMem := last_mem_of_last entries hlast
  have hlastEntryValid := hw.targetsValid lastEntry hlastMem
  have hsourceLast : sourceLastTarget entries = lastEntry.1 := by
    simp [sourceLastTarget, hlast]
  have hlastValid : canonicalAddress (sourceLastTarget entries) := by
    rw [hsourceLast]
    exact hlastEntryValid.2
  have hlastAt : oneBasedIndexAt entries (sourceLastTarget entries) =
      entries.length := by
    have hone := oneBasedIndexAt_targetAt_of_lt entries hw.targetsNodup
      (show entries.length - 1 < entries.length by omega)
    rw [targetAt_last_of_last entries hlast] at hone
    rw [hsourceLast, hone]
    omega
  have hlastNe : sourceLastTarget entries ≠ target := by
    intro heq
    have hone : oneBasedIndexAt entries target = entries.length := by
      rw [← heq]
      exact hlastAt
    rw [findEntry_oneBasedIndexAt hfind] at hone
    omega
  let idx : B256 := Nat.toB256 (index + 1)
  let len : B256 := Nat.toB256 entries.length
  let lastTarget : B256 := sourceLastTarget entries
  let oldLength : B256 := len - 1
  let assignPost := assignmentPost sevm base target 0
  let countBase := temporalSloadBase sevm assignPost (countSlot oldPauser)
  let countPost := temporalSstorePost sevm countBase (countSlot oldPauser)
    (oldCount - 1)
  let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    oldPauser.toBytes
  have hlength256 := hw.entries_length_lt_2pow256
  have hlength252 := hw.entries_length_lt_2pow252
  have hlenBound : len.toNat < 2 ^ 252 := by
    dsimp only [len]
    rw [B256.toNat_toB256_of_lt hlength256]
    exact hlength252
  have hlenNonzero : len ≠ 0 := by
    intro hz
    have h := congrArg B256.toNat hz
    rw [show len = Nat.toB256 entries.length from rfl,
      B256.toNat_toB256_of_lt hlength256] at h
    simp only [B256.toNat_zero] at h
    omega
  have hidxBound : idx.toNat < 2 ^ 252 := by
    dsimp only [idx]
    rw [B256.toNat_toB256_of_lt (by omega)]
    omega
  have hidxNonzero : idx ≠ 0 := by
    intro hz
    have h := congrArg B256.toNat hz
    rw [show idx = Nat.toB256 (index + 1) from rfl,
      B256.toNat_toB256_of_lt (by omega)] at h
    simp only [B256.toNat_zero] at h
    omega
  have hidxNeLen : idx ≠ len := by
    intro heq
    exact absurd
      (natToB256_injective_of_lt (by omega) hlength256 heq) (by omega)
  have hstorAssignment : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = oldPauser := by
    change (Devm.getStor base sevm.currentTarget).get (assignmentSlot target) =
      oldPauser
    simpa [logicalStorageOfStor, findEntry_assignmentAt hfind] using
      hw.assignments target htargetValid.2
  have hstorHole : base.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = target := by
    have h := hw.arrayWords index hindexLt
    rw [findEntry_targetAt hfind] at h
    change (Devm.getStor base sevm.currentTarget).get (arrayEntrySlot idx) =
      target
    simpa [logicalStorageOfStor, idx] using h
  have hstorTail : base.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget := by
    have h := hw.arrayWords (entries.length - 1) (by omega)
    rw [targetAt_last_of_last entries hlast,
      show entries.length - 1 + 1 = entries.length by omega] at h
    change (Devm.getStor base sevm.currentTarget).get (arrayEntrySlot len) =
      lastTarget
    simpa [logicalStorageOfStor, len, lastTarget, hsourceLast] using h
  have hstorMoved : base.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = len := by
    have h := hw.indices lastTarget hlastValid
    rw [hlastAt] at h
    change (Devm.getStor base sevm.currentTarget).get (indexSlot lastTarget) =
      len
    simpa [logicalStorageOfStor, len] using h
  have hstorIndex : base.getStorVal sevm.currentTarget (indexSlot target) =
      idx := by
    have h := hw.indices target htargetValid.2
    rw [findEntry_oneBasedIndexAt hfind] at h
    change (Devm.getStor base sevm.currentTarget).get (indexSlot target) = idx
    simpa [logicalStorageOfStor, idx] using h
  have hstorLength : base.getStorVal sevm.currentTarget arrayLengthSlot =
      len := by
    change (Devm.getStor base sevm.currentTarget).get arrayLengthSlot = len
    simpa [logicalStorageOfStor, len] using hw.lengthWord
  have hpairwise := registryAddressFamilies_pairwise htargetValid.2
    htargetValid.2 holdValid.2
  have hlastPairs := registryAddressFamilies_pairwise htargetValid.2
    hlastValid holdValid.2
  have hidxFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hidxBound
  have hlenFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 holdValid.2 hlenBound
  have hlengthNe := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 holdValid.2
  have hexpiryOldRegistry := expirySlot_ne_registryAddressFamilies
    holdValid.2 htargetValid.2 holdValid.2
  have hexpiryOldLastRegistry := expirySlot_ne_registryAddressFamilies
    holdValid.2 hlastValid holdValid.2
  have hexpiryOldIdx := expirySlot_ne_arrayFamily holdValid.2 hidxBound
  have hexpiryOldLen := expirySlot_ne_arrayFamily holdValid.2 hlenBound
  have htransport : ∀ k : B256, k ≠ countSlot oldPauser →
      k ≠ assignmentSlot target →
      countPost.getStorVal sevm.currentTarget k =
        base.getStorVal sevm.currentTarget k := by
    intro k hcountNe hassignNe
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _ k
        (pairNe hcountNe),
      temporalSloadBase_getStorVal,
      temporalSstorePost_other _ _ (assignmentSlot target) 0 _ k
        (pairNe hassignNe),
      temporalSloadBase_getStorVal]
  have hhole : countPost.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = target := by
    rw [htransport _ (Ne.symm hidxFamilies.2.2) (Ne.symm hidxFamilies.1)]
    exact hstorHole
  have hmoved : countPost.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = len := by
    rw [htransport _ hlastPairs.2.2 (Ne.symm hlastPairs.1)]
    exact hstorMoved
  have htail : countPost.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget := by
    rw [htransport _ (Ne.symm hlenFamilies.2.2) (Ne.symm hlenFamilies.1)]
    exact hstorTail
  have hindexVal : countPost.getStorVal sevm.currentTarget
      (indexSlot target) = idx := by
    rw [htransport _ hpairwise.2.2 (Ne.symm hpairwise.1)]
    exact hstorIndex
  have hlengthVal : countPost.getStorVal sevm.currentTarget arrayLengthSlot =
      len := by
    rw [htransport _ (Ne.symm hlengthNe.2.2) (Ne.symm hlengthNe.1)]
    exact hstorLength
  have hexpiryVal : countPost.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry := by
    rw [htransport _ hexpiryOldRegistry.2.2 hexpiryOldRegistry.1]
    exact hexpiry
  have hcountVal : countPost.getStorVal sevm.currentTarget
      (countSlot oldPauser) = 0 := by
    dsimp only [countPost]
    rw [temporalSstorePost_self _ _ _ _]
    exact hretired
  have hwarmTransport : ∀ k : B256,
      (sevm.currentTarget, k) ∈ base.accessedStorageKeys →
      (sevm.currentTarget, k) ∈ countPost.accessedStorageKeys := by
    intro k hk
    dsimp only [countPost, countBase, assignPost, assignmentPost,
      assignmentBase]
    rw [temporalSstorePost_accessedStorageKeys]
    refine temporalSloadBase_preserves_warm _ _ _ _ ?_
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm _ _ _ _ hk
  have hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      countPost.accessedStorageKeys := by
    dsimp only [countPost]
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_warm _ _ _
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          rw [hsize]
          decide))
  have hsize' : M'.size = 640 := by rw [hsizeM', hsize]
  have htarget' : Bytes.toB256
      (img'.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hprevious' : Bytes.toB256
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser := by
    dsimp only [img']
    rw [show 32 = oldPauser.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hcontinuation' : Bytes.toB256
      (img'.sliceD (continuationWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      decide)]
    exact hcontinuation
  let MIndex := M'.write (removedIndexWord * 32).toNat idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let removePost := indexClearPost sevm
    (swapPopClearPost sevm countPost lastTarget idx len) target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩
  let heartbeatLog : Log :=
    ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
      (0 : B256).toBytes⟩
  let post := ((temporalSstorePost sevm (removePost.addLog eventLog)
    (expirySlot oldPauser) 0).addLog heartbeatLog).setMach
      ⟨[], MLast.write 0 (0 : B256).toBytes, G⟩
  have hafterRun := afterOldPauser_swapPop_foundZeroOldLast_runCompiled dp sevm
    countPost M' img' target lastTarget idx len oldLength oldPauser oldExpiry
    oldExpiryOriginal [] (by simp) target len holeOriginal movedOriginal
    tailOriginal lengthOriginal indexOriginal holeCost movedIndexCost
    tailClearCost lengthRestoreCost indexClearCost clearCost G hwf' hreads'
    htarget' hprevious' hnew' hcontinuation' htargetValid hlastValid hlastNe
    holdValid hidxNonzero hidxBound hlenNonzero hlenBound hidxNeLen 640 3 3
    hsize' (by rw [hsize']) (by decide) (by decide) (by decide) (by decide)
    hhole hmoved htail hindexVal hlengthVal hcountVal hexpiryVal hexpiryOrig
    hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig hholeCost
    hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    hclearCost (hwarmTransport _ hwarmHole) (hwarmTransport _ hwarmMoved)
    (hwarmTransport _ hwarmTail) (hwarmTransport _ hwarmIndex)
    (hwarmTransport _ hwarmLength) hwarmCount (hwarmTransport _ hwarmExpiry)
    rfl hgasStipend hstatic
  dsimp only at hafterRun
  have hgAfter : G + 4003 + clearCost + 3 + 3 + holeCost + movedIndexCost +
      tailClearCost + lengthRestoreCost + indexClearCost =
      G + (4009 + clearCost + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost) := by omega
  rw [hgAfter] at hafterRun
  have hkernel := setPauserKernel_found_runCompiled dp sevm base M img post
    target 0 oldPauser oldCount assignmentOriginal countOriginal
    assignmentCost countCost
    (4009 + clearCost + holeCost + movedIndexCost + tailClearCost +
      lengthRestoreCost + indexClearCost) G
    hwf hreads htarget hnew htargetValid holdValid hsize.symm.le
    (by rw [hsize]) hstorAssignment
    hassignmentOrig hassignmentCost hcount hcountOrig hcountCost
    (by omega) hstatic
    (by
      simpa only [countPost, countBase, assignPost, M', MIndex, MLength,
        MLast, removePost, eventLog, heartbeatLog, post] using hafterRun)
  have hsetPauser : setPauser entries target 0 =
      some (swapPop entries index) := by
    simp [setPauser, htargetValid.1, hfind]
  obtain ⟨trace, htrace⟩ : ∃ trace,
      setPauserSourceTrace entries target 0 = some trace := by
    simp [setPauserSourceTrace, hsetPauser]
  have hrefines := setPauser_sourceTrace_refines_model htargetValid.1 htrace
  have hpostEntries : trace.postEntries = swapPop entries index := by
    rw [hsetPauser] at hrefines
    exact (Option.some.inj hrefines.1).symm
  have hwpost := hw.applySetPauserSourceTrace htargetValid.2 hzeroCanonical
    htrace
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, rfl, ?_, ?_, ?_⟩
  · have hgTotal : G + foundZeroOldLastSwapPopSetPauserKernelGas sevm base
          target oldPauser assignmentCost countCost holeCost movedIndexCost
          tailClearCost lengthRestoreCost indexClearCost clearCost =
        G + (4009 + clearCost + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) +
          foundSetPauserKernelPrefixGas sevm base target 0 oldPauser
            assignmentCost countCost := by
      dsimp only [foundZeroOldLastSwapPopSetPauserKernelGas,
        foundSetPauserKernelPrefixGas]
      omega
    rw [hgTotal]
    exact hkernel
  · have logs_setMach (d : Devm) (mach : Mach) :
        (d.setMach mach).logs = d.logs := rfl
    have logs_addLog (d : Devm) (log : Log) :
        (d.addLog log).logs = d.logs ++ [log] := rfl
    dsimp only [post, removePost, countPost, countBase, assignPost,
      assignmentPost, assignmentBase, eventLog, heartbeatLog]
    rw [logs_setMach, logs_addLog, temporalSstorePost_logs, logs_addLog]
    simp only [indexClearPost, lengthWritePost,
      swapPopClearPost, indexWritePost, entryWritePost,
      temporalSstorePost_logs, temporalSloadBase_logs, List.append_assoc,
      List.cons_append, List.nil_append]
  · dsimp only [post]
    rw [Devm.getStorVal_setMach, getStorVal_addLog]
    exact temporalSstorePost_self _ _ _ _
  · intro pauser hpauser hne
    have hexpiryIdx := expirySlot_ne_arrayFamily hpauser hidxBound
    have hexpiryLen := expirySlot_ne_arrayFamily hpauser hlenBound
    have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
      hpauser htargetValid.2 holdValid.2
    have hexpiryLastRegistry := expirySlot_ne_registryAddressFamilies
      hpauser hlastValid holdValid.2
    have hexpiryOther : expirySlot pauser ≠ expirySlot oldPauser :=
      expirySlotNe hpauser holdValid.2 hne
    calc
      post.getStorVal sevm.currentTarget (expirySlot pauser) =
          (temporalSstorePost sevm (removePost.addLog eventLog)
            (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
              (expirySlot pauser) := by
        dsimp only [post]
        rw [Devm.getStorVal_setMach, getStorVal_addLog]
      _ = base.getStorVal sevm.currentTarget (expirySlot pauser) := by
        rw [temporalSstorePost_other _ _ (expirySlot oldPauser) 0 _
            (expirySlot pauser) (pairNe hexpiryOther),
          getStorVal_addLog]
        dsimp only [removePost, countPost, countBase, assignPost,
          assignmentPost, assignmentBase]
        simp only [indexClearPost, lengthWritePost,
          swapPopClearPost, indexWritePost, entryWritePost]
        rw [temporalSstorePost_other _ _ (indexSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.1),
          temporalSstorePost_other _ _ arrayLengthSlot oldLength _
            (expirySlot pauser) (pairNe hexpiryLen.1),
          temporalSstorePost_other _ _ (arrayEntrySlot len) 0 _
            (expirySlot pauser) (pairNe hexpiryLen.2),
          temporalSstorePost_other _ _ (indexSlot lastTarget) idx _
            (expirySlot pauser) (pairNe hexpiryLastRegistry.2.1),
          temporalSstorePost_other _ _ (arrayEntrySlot idx) lastTarget _
            (expirySlot pauser) (pairNe hexpiryIdx.2),
          temporalSstorePost_other _ _ (countSlot oldPauser) (oldCount - 1) _
            (expirySlot pauser) (pairNe hexpiryRegistry.2.2),
          temporalSloadBase_getStorVal,
          temporalSstorePost_other _ _ (assignmentSlot target) 0 _
            (expirySlot pauser) (pairNe hexpiryRegistry.1),
          temporalSloadBase_getStorVal]

/-- Exact production-body reserve for unregistering a recorded target that is
not the array's last entry, retiring the old pauser. -/
def foundZeroOldLastSwapPopRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost : Nat) : Nat :=
  221 + foundZeroOldLastSwapPopSetPauserKernelGas sevm base target oldPauser
    assignmentCost countCost holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost clearCost

/-- Exact successful production body for the last combination: the removed
target is not the array's last entry (`index + 1 < entries.length`) and the old
pauser is retired (`oldCount - 1 = 0`). -/
theorem registerPauser_body_foundZeroOldLastSwapPop_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (index + 1))) ∈ base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget,
      indexSlot (sourceLastTarget entries)) ∈ base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + foundZeroOldLastSwapPopRegisterBodyGas sevm base target oldPauser
            assignmentCost countCost holeCost movedIndexCost tailClearCost
            lengthRestoreCost indexClearCost clearCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
           (0 : B256).toBytes⟩] ∧
      post.getStorVal sevm.currentTarget (expirySlot oldPauser) = 0 ∧
      ∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  rcases registerMemory_spec target 0 with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      _hpreviousRead, hcontinuationRead⟩
  rcases setPauserKernel_foundZeroOldLastSwapPop_runCompiled dp sevm base
      (registerMemory target 0) (registerImage target 0)
      entries target index oldPauser oldCount oldExpiry oldExpiryOriginal
      assignmentOriginal countOriginal holeOriginal movedOriginal tailOriginal
      lengthOriginal indexOriginal assignmentCost countCost holeCost
      movedIndexCost tailClearCost lengthRestoreCost indexClearCost clearCost G
      hw hfind hnotLast hwf hreads htargetRead hnewRead hcontinuationRead
      htargetValid holdValid hsize hassignmentOrig hassignmentCost hcount
      hcountOrig hcountCost hretired hexpiry hexpiryOrig hclearCost hholeOrig
      hmovedOrig htailOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost
      htailClearCost hlengthRestoreCost hindexClearCost hwarmHole hwarmMoved
      hwarmTail hwarmIndex hwarmLength hwarmExpiry hgasStipend hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hkernel, hgas, hlogs,
      holdExpiryPost, hexpiries⟩
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, hgas, hlogs,
    holdExpiryPost, hexpiries⟩
  have htargetMask := canonicalAddress_mask_zero htargetValid.2
  have hnewMask : addressMask &&& (0 : B256) = 0 := by decide +kernel
  have hbody := registerPauser_body_from_kernel_runCompiled dp sevm base target
    (G + foundZeroOldLastSwapPopSetPauserKernelGas sevm base target oldPauser
      assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost) post hdata hadmin hargTarget
    hargNew htargetMask hnewMask hkernel
  simp only [foundZeroOldLastSwapPopRegisterBodyGas]
  have hg :
      G + (221 + foundZeroOldLastSwapPopSetPauserKernelGas sevm base target
        oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost clearCost) =
      (G + foundZeroOldLastSwapPopSetPauserKernelGas sevm base target
        oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost clearCost) + 221 := by
    omega
  rw [hg]
  exact hbody

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-runtime success for the last combination: an interior
removal that retires the old pauser. -/
theorem registerPauser_runCompiledTo_foundZeroOldLastSwapPop
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hholeOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (index + 1))) ∈ base.accessedStorageKeys)
    (hwarmMoved : (sevm.currentTarget,
      indexSlot (sourceLastTarget entries)) ∈ base.accessedStorageKeys)
    (hwarmTail : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 entries.length)) ∈ base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            foundZeroOldLastSwapPopRegisterBodyGas sevm base target oldPauser
              assignmentCost countCost holeCost movedIndexCost tailClearCost
              lengthRestoreCost indexClearCost clearCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
           (0 : B256).toBytes⟩] ∧
      post.getStorVal sevm.currentTarget (expirySlot oldPauser) = 0 ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_foundZeroOldLastSwapPop_runCompiled dp sevm base
      entries target index oldPauser oldCount oldExpiry oldExpiryOriginal
      assignmentOriginal countOriginal holeOriginal movedOriginal tailOriginal
      lengthOriginal indexOriginal assignmentCost countCost holeCost
      movedIndexCost tailClearCost lengthRestoreCost indexClearCost clearCost G
      hbodyData hadmin hargTarget hargNew hw hfind hnotLast htargetValid
      holdValid hassignmentOrig hassignmentCost hcount hcountOrig hcountCost
      hretired hexpiry hexpiryOrig hclearCost hholeOrig hmovedOrig htailOrig
      hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
      hlengthRestoreCost hindexClearCost hwarmHole hwarmMoved hwarmTail
      hwarmIndex hwarmLength hwarmExpiry hgasStipend hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hbody, hgas, hlogs,
      holdExpiryPost, hexpiries⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (foundZeroOldLastSwapPopRegisterBodyGas sevm base target oldPauser
        assignmentCost countCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost clearCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
    holdExpiryPost, hexpiries, hcompile⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact clean direct-message effects for the last combination of the
chronology, derived from the generated-runtime execution: the removed target is
not the array's last entry (`index + 1 < entries.length`) and the old pauser is
retired (`oldCount - 1 = 0`).  The last array entry is moved into the hole and
its reverse index repaired, two records are emitted in order, and exactly one
expiry cell moves — the retired pauser's, to `0`. -/
theorem registerPauser_foundZeroOldLastSwapPop_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr} {final settled : Devm}
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser oldCount oldExpiry oldExpiryOriginal : B256)
    (assignmentOriginal countOriginal holeOriginal movedOriginal
      tailOriginal lengthOriginal indexOriginal : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost clearCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target 0)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      foundZeroOldLastSwapPopRegisterBodyGas (initSevm msg) (initDevm msg)
        target oldPauser assignmentCost countCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost clearCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor (initDevm msg) ca)) entries)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnotLast : index + 1 < entries.length)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser 0 =
      assignmentCost)
    (hcount : (assignmentPost (initSevm msg) (initDevm msg)
      target 0).getStorVal ca (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hretired : oldCount - 1 = 0)
    (hexpiry : (initDevm msg).getStorVal ca
      (expirySlot oldPauser) = oldExpiry)
    (hexpiryOrig : getOrigStorVal (initSevm msg) ca
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (hholeOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 (index + 1))) = holeOriginal)
    (hmovedOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot (sourceLastTarget entries)) = movedOriginal)
    (htailOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 entries.length)) = tailOriginal)
    (hindexOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal (initSevm msg) ca arrayLengthSlot =
      lengthOriginal)
    (hholeCost : sstoreValueCost holeOriginal target
      (sourceLastTarget entries) = holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (index + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal
      (sourceLastTarget entries) 0 = tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 entries.length - 1) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (index + 1)) 0 = indexClearCost)
    (hwarmHole : (ca, arrayEntrySlot (Nat.toB256 (index + 1))) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmMoved : (ca, indexSlot (sourceLastTarget entries)) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmTail : (ca, arrayEntrySlot (Nat.toB256 entries.length)) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmIndex : (ca, indexSlot target) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmLength : (ca, arrayLengthSlot) ∈
      (initDevm msg).accessedStorageKeys)
    (hwarmExpiry : (ca, expirySlot oldPauser) ∈
      (initDevm msg).accessedStorageKeys)
    (hgasStipend : gCallStipend < G + 1402 + clearCost)
    (hstatic : (initSevm msg).isStatic = false)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    ∃ trace,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = swapPop entries index ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor (initDevm msg) ca) trace.writes))
        trace.postEntries ∧
      settled.gasLeft = G ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, oldPauser, 0], []⟩,
         ⟨ca, [heartbeatUpdatedEvent, oldPauser], (0 : B256).toBytes⟩] ∧
      settled.getStorVal ca (expirySlot oldPauser) = 0 ∧
      ∀ pauser, canonicalAddress pauser → pauser ≠ oldPauser →
        settled.getStorVal ca (expirySlot pauser) =
          (initDevm msg).getStorVal ca (expirySlot pauser) := by
  have hdataInit : (initSevm msg).data =
      registerPauserCalldata target 0 := by
    simpa [initSevm] using hdata
  rcases registerPauserCalldata_spec (initSevm msg) target 0 hdataInit with
    ⟨hdataLength, hselector, hargTarget, hargNew⟩
  have hvalueInit : (initSevm msg).value = 0 := by
    simpa [initSevm] using hvalue
  have hownerInit : (initSevm msg).currentTarget = ca := by
    simpa [initSevm] using howner
  have hcodeAddressInit : (initSevm msg).codeAddress =
      some (initSevm msg).currentTarget := by
    simpa [initSevm, howner] using hcodeAddress
  have hcodeInit : (initSevm msg).code.toList =
      lidoCircuitBreakerCode dp := by
    simpa [initSevm] using hcode
  have hadminInit : (initSevm msg).caller.toB256 = dp.admin := by
    simpa [initSevm] using hadmin
  rcases registerPauser_runCompiledTo_foundZeroOldLastSwapPop dp (initSevm msg)
      (initDevm msg) entries target index oldPauser oldCount oldExpiry
      oldExpiryOriginal assignmentOriginal countOriginal holeOriginal
      movedOriginal tailOriginal lengthOriginal indexOriginal assignmentCost
      countCost holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost clearCost G hdataLength hvalueInit hselector
      hcodeAddressInit hcodeInit hadminInit hargTarget hargNew
      (by simpa [hownerInit] using hw) hfind hnotLast htargetValid holdValid
      (by simpa [hownerInit] using hassignmentOrig) hassignmentCost
      (by simpa [hownerInit] using hcount)
      (by simpa [hownerInit] using hcountOrig) hcountCost hretired
      (by simpa [hownerInit] using hexpiry)
      (by simpa [hownerInit] using hexpiryOrig) hclearCost
      (by simpa [hownerInit] using hholeOrig)
      (by simpa [hownerInit] using hmovedOrig)
      (by simpa [hownerInit] using htailOrig)
      (by simpa [hownerInit] using hindexOrig)
      (by simpa [hownerInit] using hlengthOrig) hholeCost hmovedIndexCost
      htailClearCost hlengthRestoreCost hindexClearCost
      (by simpa [hownerInit] using hwarmHole)
      (by simpa [hownerInit] using hwarmMoved)
      (by simpa [hownerInit] using hwarmTail)
      (by simpa [hownerInit] using hwarmIndex)
      (by simpa [hownerInit] using hwarmLength)
      (by simpa [hownerInit] using hwarmExpiry) hgasStipend hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
      holdExpiryPost, hexpiries, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          foundZeroOldLastSwapPopRegisterBodyGas (initSevm msg) (initDevm msg)
            target oldPauser assignmentCost countCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost clearCost⟩ =
        initDevm msg := by
    rw [← hgasEntry]
    rfl
  have hrunEntry : Prog.RunCompiledTo (initSevm msg) (initDevm msg)
      (runtime dp) (.ok post) := by
    rw [hentryState] at hrun
    exact hrun
  have hexecEq : exec ⟨0, initSevm msg, initDevm msg⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrunEntry hcompile
  obtain ⟨hpostExec⟩ :=
    (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok post)).mpr
      hexecEq
  change Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hsettledFinal := registerPauser_success_settles_cleanly dp
    htargetOwner howner hcodeAddress hcode hvalue hdata hprocess hclean
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  refine ⟨trace, htrace, hpostEntries, ?_, hgas, ?_, ?_, ?_⟩
  · simpa [hownerInit] using hwpost
  · simpa [hownerInit] using hlogs
  · simpa [hownerInit] using holdExpiryPost
  · intro pauser hpauser hne
    simpa [hownerInit] using hexpiries pauser hpauser hne

end Blanc.LidoCircuitBreaker
