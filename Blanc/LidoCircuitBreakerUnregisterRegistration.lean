import Blanc.LidoCircuitBreakerRegistrySubstrate

/-!
Found-zero unregistration chronology for the Lido CircuitBreaker.

The target is already registered and the new pauser's count is zero, so
`setPauser` removes the target and retains the old pauser, taking the
seven-write found-zero chronology.
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
    hnextBound entrySize indexExtCost lengthExtCost hsize halign hentryLow
    hentryHigh hindexExtCost hlengthExtCost
    harray hindex hlength harrayOrig hindexOrig
    hlengthOrig hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost
    hindexClearCost hwarmArray hwarmIndex hwarmLength hsub hgasFinal hstatic
    (by simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog]
      using hfinish)
  have hg : G + 2108 + 443 + indexExtCost + lengthExtCost + holeCost +
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
    hwf hreads htarget hnew htargetValid holdValid hsize hstorAssignment
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

/-- Exact production-body reserve for unregistering a recorded target that is
already the array's last entry, with the old pauser retained. -/
def foundZeroRetainedLastRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target oldPauser : B256)
    (assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost : Nat) : Nat :=
  221 + foundZeroRetainedLastSetPauserKernelGas sevm base target oldPauser
    assignmentCost countCost holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- The four scratch writes `registerPauser`'s body performs before entering
the kernel: the two decoded arguments and the two zero words.  The staging is
chronology-independent, so the kernel run is taken as a hypothesis. -/
private theorem registerPauser_stageArgs_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target newPauser : B256) (kernelGas : Nat) (post : Devm)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = newPauser)
    (hkernel : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], registerMemory target newPauser, kernelGas⟩)
      setPauserKernel post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, kernelGas + 112⟩)
      (arg 0 +++ mstoreAt targetWord +++
        arg 1 +++ mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 0 ::: mstoreAt continuationWord +++
        .call setPauserSlot) post := by
  have hM1Size (w : B256) :
      (Mem.empty.write (targetWord * 32).toNat w.toBytes).size = 544 := by
    rw [Mem.size_write_word_at]
    decide +kernel
  have hM2Size (w₁ w₂ : B256) :
      ((Mem.empty.write (targetWord * 32).toNat w₁.toBytes).write
        (newPauserWord * 32).toNat w₂.toBytes).size = 576 := by
    rw [Mem.size_write_word_at, hM1Size]
    decide +kernel
  have hM3Size (w₁ w₂ : B256) :
      (((Mem.empty.write (targetWord * 32).toNat w₁.toBytes).write
        (newPauserWord * 32).toNat w₂.toBytes).write
        (previousPauserWord * 32).toNat (0 : B256).toBytes).size = 608 := by
    rw [Mem.size_write_word_at, hM2Size]
    decide +kernel
  unfold arg cdl
  func_run (15) [51, 3, 3, 3]
  -- Each extension goal takes exactly the alternative that fits it, in the
  -- order `func_run` emits them.  A `first` combinator over all four cost
  -- 46.4 s here (measured): a failed `exact` still unifies `N.size = n`
  -- against the write tower, so every goal paid for the alternatives it did
  -- not need.  Ordered `case h_ext` blocks brought the same proof to 5.1 s.
  case h_ext => exact Devm.extCost_of_size (n := 0) rfl (by decide +kernel)
  case h_ext => exact Devm.extCost_of_size (n := 544) (hM1Size _) (by decide +kernel)
  case h_ext =>
    exact Devm.extCost_of_size (n := 576) (hM2Size _ _) (by decide +kernel)
  case h_ext =>
    exact Devm.extCost_of_size (n := 608) (hM3Size _ _) (by decide +kernel)
  case h_body =>
    rw [hargTarget, hargNew]
    change Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], registerMemory target newPauser, kernelGas⟩)
      setPauserKernel post
    exact hkernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
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
  have hstage := registerPauser_stageArgs_runCompiled dp sevm base target 0
    (G + foundZeroRetainedLastSetPauserKernelGas sevm base target oldPauser
      assignmentCost countCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost) post hargTarget hargNew hkernel
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, hgas, hlogs,
    hexpiries⟩
  have htargetMask := canonicalAddress_mask_zero htargetValid.2
  have hnewMask : (0 : B256) &&& addressMask = 0 := by decide +kernel
  unfold registerPauser requireStaticArgs canonicalAddressArg onlyAdmin arg cdl
    checkNonAddress pushAddressMask pushDeployWord
  func_run (24) [0, ~~~(0 : B256), addressMask, 0,
    ~~~(0 : B256), addressMask, 0, 1]
  all_goals try { rw [hargTarget]; exact htargetMask }
  all_goals try { rw [hargNew]; exact hnewMask }
  all_goals try { simp [hadmin, B256.eqCheck] }
  all_goals first
    | (simp only [Devm.gasLeft_setMach, foundZeroRetainedLastRegisterBodyGas]
       norm_num [gBase, gVerylow, gHigh, gMid, gJumpdest]
       omega)
    | skip
  case h_arm =>
    simp only [foundZeroRetainedLastRegisterBodyGas]
    have hg : G + (221 + foundZeroRetainedLastSetPauserKernelGas sevm base
          target oldPauser assignmentCost countCost holeCost movedIndexCost
          tailClearCost lengthRestoreCost indexClearCost) - 109 =
        G + foundZeroRetainedLastSetPauserKernelGas sevm base target oldPauser
          assignmentCost countCost holeCost movedIndexCost tailClearCost
          lengthRestoreCost indexClearCost + 112 := by omega
    rw [hg]
    simpa only [arg, cdl] using hstage

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

end Blanc.LidoCircuitBreaker
