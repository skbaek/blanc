import Blanc.LidoCircuitBreakerRegistrySubstrate

/-!
Absent-zero registration chronology for the Lido CircuitBreaker.

The target is absent and the new pauser *address* is zero, so `setPauser`
appends the target and then removes it again, taking the nine-write absent-zero
chronology.  This is the `0 → 0` partition; no entry count is constrained.

**What the settled-effects theorem pins, and what it does not.**  It pins
`gasLeft` exactly, the new pauser's expiry cell, and the emitted record list
exactly (`logs = base.logs ++ [...]`).  The Registry cells the flow writes are
characterised **model-side only**, by `RegistryWitness` over
`applyRegistryWrites (Devm.getStor base ca) trace.writes`, with **no** conjunct
relating the settled state's storage to that model store.  That conjunct is
discharged by the source-trace witness above, whose premises are the model's
alone -- it would hold verbatim if the compiled program wrote nothing.  Sitting
in the same conjunction as `settled.gasLeft` and `settled.logs` it reads like an
execution effect and is not one.  Supplying the operational-to-model storage
equation is an open unit.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst


/-! ## Absent-target zero-pauser registration -/

/-- The absent-target/zero-pauser model branch derives the exact nine-write
append-then-remove chronology while restoring the original Registry entries. -/
theorem absentZeroRegistration_sourceTrace_witness
    {s : Stor} {entries : List Entry} {target : B256}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = none) :
    ∃ trace : SetPauserSourceTrace,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = entries ∧
      trace.writes =
        [(assignmentSlot target, 0),
         (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
         (indexSlot target, Nat.toB256 (entries.length + 1)),
         (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
         (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
         (indexSlot target, Nat.toB256 (entries.length + 1)),
         (arrayEntrySlot (Nat.toB256 (entries.length + 1)), 0),
         (arrayLengthSlot, Nat.toB256 entries.length),
         (indexSlot target, 0)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites s trace.writes)) entries := by
  have hpost : setPauser entries target 0 = some entries := by
    simp [setPauser, htarget.1, hfind]
  have htrace : setPauserSourceTrace entries target 0 =
      some { postEntries := entries
             writes :=
               [(assignmentSlot target, 0),
                (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
                (indexSlot target, Nat.toB256 (entries.length + 1)),
                (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
                (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
                (indexSlot target, Nat.toB256 (entries.length + 1)),
                (arrayEntrySlot (Nat.toB256 (entries.length + 1)), 0),
                (arrayLengthSlot, Nat.toB256 entries.length),
                (indexSlot target, 0)] } := by
    simp [setPauserSourceTrace, hpost,
      setPauserSourceWrites_absent_zero entries target htarget.1 hfind]
  refine ⟨_, htrace, rfl, rfl, ?_⟩
  exact hw.applyAbsentZeroWrites htarget hfind

private theorem registerAfterSet_absentZero_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (carry : B256) (G : Nat)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[carry], M, G + 46⟩)
      registerAfterSet (base.setMach ⟨[carry], M, G⟩) := by
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
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0 := by
    rw [Mem.Reads.read hreads]
    exact hprevious
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = 0 := by
    rw [Mem.Reads.read hreads]
    exact hnew
  unfold registerAfterSet
  func_run (10) [3, 1, 3, 1]
  all_goals try { simp [hpreviousValue, B256.eqCheck] }
  all_goals try {
    rw [Devm.extCost_zero_of_le halign hpreviousCovered]
    norm_num [gVerylow] }
  all_goals try {
    rw [hpreviousMemory]
    rw [Devm.extCost_zero_of_le halign hnewCovered]
    norm_num [gVerylow] }
  case h_val =>
    rw [hpreviousMemory, hnewValue]
    simp [B256.eqCheck]
  case h_arm =>
    rw [hpreviousMemory, hnewMemory]
    exact Func.RunCompiled.last rfl

private theorem finishSetPauser_absentZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (target carry : B256) (G : Nat)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hstatic : sevm.isStatic = false) :
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[carry], M, G + 1981⟩) finishSetPauser
      ((base.addLog eventLog).setMach ⟨[carry], M, G⟩) := by
  dsimp only
  have hregister := registerAfterSet_absentZero_runCompiled
    ((runtime dp).main :: (runtime dp).aux) sevm
    (base.addLog ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩)
    M img carry G hreads hprevious hnew hsize halign
  have h := finishSetPauser_registerAfterSet_runCompiled dp sevm base M img
    target 0 0 [carry] (G + 46)
    ((base.addLog ⟨sevm.currentTarget,
      [pauserSetEvent, target, 0, 0], []⟩).setMach ⟨[carry], M, G⟩)
    (by simp) hreads htarget hprevious hnew hcontinuation hsize halign
    hstatic hregister
  have hg : G + 46 + 1935 = G + 1981 := by omega
  rw [hg] at h
  exact h

private theorem afterOldPauser_absentZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next carry : B256)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (hsize : M.size = 704) (halign : M.size % 32 = 0)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = next)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal next next =
      movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal next 0 =
      indexClearCost)
    (hwarmArray : (sevm.currentTarget, arrayEntrySlot next) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hsub : next - 1 = oldLength)
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[carry], M,
        G + 2459 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost⟩)
      afterOldPauser
      (((indexClearPost sevm
          (entryClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
  dsimp only
  let fs := (runtime dp).main :: (runtime dp).aux
  let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    next.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    next.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    target.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
  have hwfIndex : Mem.Wf MIndex := hwf.write _ _
  have hreadsIndex : Mem.Reads MIndex imgIndex :=
    Mem.Reads.write hwf hreads _ _
  have hwfLength : Mem.Wf MLength := hwfIndex.write _ _
  have hreadsLength : Mem.Reads MLength imgLength :=
    Mem.Reads.write hwfIndex hreadsIndex _ _
  have hreadsLast : Mem.Reads MLast imgLast :=
    Mem.Reads.write hwfLength hreadsLength _ _
  have hsizeIndex : MIndex.size = 704 := by
    dsimp only [MIndex]
    rw [Mem.size_write_word_at,
      show (removedIndexWord * 32).toNat + 32 = 672 by decide, hsize]
    split <;> omega
  have hsizeLength : MLength.size = 704 := by
    dsimp only [MLength]
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide,
      hsizeIndex]
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
      (imgLast.sliceD (previousPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hprevious
  have hnewLast : Bytes.toB256
      (imgLast.sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hnew
  have hcontinuationLast : Bytes.toB256
      (imgLast.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hcontinuation
  let tailPost := entryClearPost sevm base target next
  let removePost := indexClearPost sevm tailPost target oldLength
  have hfinish := finishSetPauser_absentZero_runCompiled dp sevm removePost
    MLast imgLast target carry G hreadsLast htargetLast hpreviousLast
    hnewLast hcontinuationLast (by rw [hsizeLast]; decide) halignLast hstatic
  have hremove := removeTarget_runCompiled dp sevm base M img
    target oldLength next 0 [carry] (by simp) arrayOriginal indexOriginal
    lengthOriginal
    holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost
    1981 G hwf hreads htarget htargetValid
    hnextNonzero hnextBound 704 0 0 4 hsize halign (by decide) (by decide)
    (by decide) (by decide) harray hindex hlength harrayOrig
    hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
    hlengthRestoreCost hindexClearCost hwarmArray hwarmIndex hwarmLength
    hsub hgasFinal hstatic
    (by simpa only [MIndex, MLength, MLast, tailPost, removePost, eventLog]
      using hfinish)
  have h := afterOldPauser_removeTarget_runCompiled dp sevm base M img
    [carry]
    (G + 2424 + holeCost + movedIndexCost + tailClearCost +
      lengthRestoreCost + indexClearCost)
    (((indexClearPost sevm
        (entryClearPost sevm base target next)
        target oldLength).addLog eventLog).setMach ⟨[carry], MLast, G⟩)
    (by simp) hreads hnew (by omega) halign
    (by simpa only [fs, MIndex, MLength, MLast, eventLog, Nat.add_zero]
      using hremove)
  have hg : G + 2424 + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost + 35 =
      G + 2459 + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost := by omega
  rw [hg] at h
  exact h

private theorem appendTarget_then_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (target length next : B256)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (arrayCost indexCost lengthCost afterGas : Nat)
    (post : Devm)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hsize : M.size = 640)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (hlength : base.getStorVal sevm.currentTarget arrayLengthSlot = length)
    (hlengthNext : (1 : B256) + length = next)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget, arrayEntrySlot next) ∈
      base.accessedStorageKeys)
    (hindex : base.getStorVal sevm.currentTarget (indexSlot target) = 0)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0 next = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal length next = lengthCost)
    (hgasAfter : gCallStipend < afterGas + 12)
    (hstatic : sevm.isStatic = false)
    (hafter :
      let lengthBase := temporalSloadBase sevm base arrayLengthSlot
      let arrayPost := temporalSstorePost sevm lengthBase
        (arrayEntrySlot next) target
      let indexPost := temporalSstorePost sevm arrayPost
        (indexSlot target) next
      let lengthPost := temporalSstorePost sevm indexPost
        arrayLengthSlot next
      let M' := M.write (arrayLengthWord * 32).toNat next.toBytes
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (lengthPost.setMach ⟨[next], M', afterGas⟩)
        afterOldPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M,
        afterGas + 75 + arrayLengthMemoryCost M +
          temporalSloadCost sevm base arrayLengthSlot +
          arrayCost + indexCost + lengthCost⟩)
      appendTarget post := by
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let lengthBase := temporalSloadBase sevm base arrayLengthSlot
  let arrayPost := temporalSstorePost sevm lengthBase arrayKey target
  let indexPost := temporalSstorePost sevm arrayPost indexKey next
  let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
  have harrayFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 htargetValid.2 hnextBound
  have hlengthFamilies := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 htargetValid.2
  have hlengthArray :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnextNonzero hnextBound
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have hlengthBase : lengthBase.getStorVal sevm.currentTarget
      arrayLengthSlot = length := by
    rw [temporalSloadBase_getStorVal]
    exact hlength
  have hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      lengthBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm base arrayLengthSlot
  have harrayBase : lengthBase.getStorVal sevm.currentTarget arrayKey = 0 := by
    rw [temporalSloadBase_getStorVal]
    exact harray
  have hwarmArrayBase : (sevm.currentTarget, arrayKey) ∈
      lengthBase.accessedStorageKeys :=
    temporalSloadBase_preserves_warm sevm base arrayLengthSlot arrayKey
      hwarmArray
  have hindexArray : arrayPost.getStorVal sevm.currentTarget indexKey = 0 := by
    rw [temporalSstorePost_other sevm lengthBase arrayKey target
      sevm.currentTarget indexKey (pairNe (by
        simpa only [arrayKey, indexKey] using harrayFamilies.2.1))]
    rw [temporalSloadBase_getStorVal]
    exact hindex
  have hwarmIndexArray : (sevm.currentTarget, indexKey) ∈
      arrayPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm sevm base arrayLengthSlot
      indexKey hwarmIndex
  have hlengthIndex : indexPost.getStorVal sevm.currentTarget
      arrayLengthSlot = length := by
    rw [temporalSstorePost_other sevm arrayPost indexKey next
      sevm.currentTarget arrayLengthSlot (pairNe (by
        simpa only [indexKey] using Ne.symm hlengthFamilies.2.1))]
    rw [temporalSstorePost_other sevm lengthBase arrayKey target
      sevm.currentTarget arrayLengthSlot (pairNe hlengthArray)]
    exact hlengthBase
  have hwarmLengthIndex : (sevm.currentTarget, arrayLengthSlot) ∈
      indexPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmLength
  let M' := M.write (arrayLengthWord * 32).toNat next.toBytes
  let img' := Bytes.writeAt img (arrayLengthWord * 32).toNat next.toBytes
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsize' : M'.size = 704 := by
    dsimp only [M']
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide +kernel,
      hsize]
    decide +kernel
  have halign' : M'.size % 32 = 0 := by rw [hsize']
  have harrayLengthOff' :
      (arrayLengthWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsize']
    decide
  have sliceBefore {word : B256}
      (hbefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat) :
      Bytes.toB256 (img'.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hbefore]
  have htarget' : Bytes.toB256
      (img'.sliceD (targetWord * 32).toNat 32 0) = target :=
    (sliceBefore (by decide)).trans htarget
  have hafter' : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (lengthPost.setMach ⟨[next], M', afterGas⟩)
      afterOldPauser post := by
    simpa only [lengthPost, indexPost, arrayPost, lengthBase, M', arrayKey,
      indexKey] using hafter
  let fs := (runtime dp).main :: (runtime dp).aux
  have hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser := by
    simp [fs, runtime, aux, afterOldPauserSlot]
  have hafterCall : Func.RunCompiled fs sevm
      (lengthPost.setMach ⟨[next], M', afterGas + 12⟩)
      (.call afterOldPauserSlot) post := by
    apply Func.RunCompiled.call hafterLookup
      (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := lengthPost.setMach ⟨[next], M', afterGas + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := afterGas)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hafter'
  have hstoreLength : Func.RunCompiled fs sevm
      (indexPost.setMach ⟨[arrayLengthSlot, next, next], M',
        afterGas + 12 + lengthCost⟩)
      (Ninst.sstore ::: .call afterOldPauserSlot) post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hlengthIndex hlengthOrig hlengthCost
        hwarmLengthIndex (by omega) hstatic)
      hafterCall
  have hlengthTail : Func.RunCompiled fs sevm
      (indexPost.setMach ⟨[next], M', afterGas + 21 + lengthCost⟩)
      (loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (3) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign' harrayLengthOff']
      norm_num [gVerylow]
    case a =>
      have hmem : (M'.read (arrayLengthWord * 32).toNat 32).2 = M' := by
        rw [Mem.read_snd_eq_self
          (memExtSize_of_le halign' harrayLengthOff')]
      have hval : (M'.read (arrayLengthWord * 32).toNat 32).1.toB256 =
          next := by
        rw [Mem.Reads.read hreads']
        dsimp only [img']
        rw [show 32 = next.toBytes.length by rw [B256.length_toBytes],
          Bytes.sliceD_writeAt, B256.toB256_toBytes]
      rw [hval, hmem]
      have hg : afterGas + 21 + lengthCost - 9 =
          afterGas + 12 + lengthCost := by omega
      rw [hg]
      exact hstoreLength
  have hstoreIndex : Func.RunCompiled fs sevm
      (arrayPost.setMach ⟨[indexKey, next, next], M',
        afterGas + 21 + lengthCost + indexCost⟩)
      (Ninst.sstore ::: loadWord arrayLengthWord +++
        pushB256 arrayLengthSlot ::: Ninst.sstore :::
        .call afterOldPauserSlot) post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hindexArray hindexOrig hindexCost
        hwarmIndexArray (by omega) hstatic)
      hlengthTail
  have htargetOff' : (targetWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsize']
    decide
  have htargetMem : (M'.read (targetWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' htargetOff')]
  have hlengthMem : (M'.read (arrayLengthWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self
      (memExtSize_of_le halign' harrayLengthOff')]
  have htargetVal : (M'.read (targetWord * 32).toNat 32).1.toB256 =
      target := by rw [Mem.Reads.read hreads']; exact htarget'
  have hlengthVal :
      (M'.read (arrayLengthWord * 32).toNat 32).1.toB256 = next := by
    rw [Mem.Reads.read hreads']
    dsimp only [img']
    rw [show 32 = next.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hindexTag : Func.RunCompiled fs sevm
      (arrayPost.setMach ⟨[target, next, next], M',
        afterGas + 27 + lengthCost + indexCost⟩)
      (tagTop indexRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (2) [indexKey]
    case a =>
      have hg : afterGas + 27 + lengthCost + indexCost - 6 =
          afterGas + 21 + lengthCost + indexCost := by omega
      rw [hg]
      exact hstoreIndex
  have hindexTargetLoad : Func.RunCompiled fs sevm
      (arrayPost.setMach ⟨[next, next], M',
        afterGas + 33 + lengthCost + indexCost⟩)
      (loadWord targetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign' htargetOff']
      norm_num [gVerylow]
    case a =>
      rw [htargetVal, htargetMem]
      have hg : afterGas + 33 + lengthCost + indexCost - 6 =
          afterGas + 27 + lengthCost + indexCost := by omega
      rw [hg]
      exact hindexTag
  have hindexTail : Func.RunCompiled fs sevm
      (arrayPost.setMach ⟨[next], M',
        afterGas + 39 + lengthCost + indexCost⟩)
      (loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign' harrayLengthOff']
      norm_num [gVerylow]
    case a =>
      rw [hlengthVal, hlengthMem]
      have hg : afterGas + 39 + lengthCost + indexCost - 6 =
          afterGas + 33 + lengthCost + indexCost := by omega
      rw [hg]
      exact hindexTargetLoad
  have hstoreArray : Func.RunCompiled fs sevm
      (lengthBase.setMach ⟨[arrayKey, target, next], M',
        afterGas + 39 + lengthCost + indexCost + arrayCost⟩)
      (Ninst.sstore ::: loadWord arrayLengthWord +++ targetIndexKey +++
        Ninst.sstore ::: loadWord arrayLengthWord +++
        pushB256 arrayLengthSlot ::: Ninst.sstore :::
        .call afterOldPauserSlot) post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled harrayBase harrayOrig harrayCost
        hwarmArrayBase (by omega) hstatic)
      hindexTail
  have harrayTag : Func.RunCompiled fs sevm
      (lengthBase.setMach ⟨[next, target, next], M',
        afterGas + 45 + arrayCost + indexCost + lengthCost⟩)
      (tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (2) [arrayKey]
    case a =>
      have hg : afterGas + 45 + arrayCost + indexCost + lengthCost - 6 =
          afterGas + 39 + lengthCost + indexCost + arrayCost := by omega
      rw [hg]
      exact hstoreArray
  have harrayLengthLoad : Func.RunCompiled fs sevm
      (lengthBase.setMach ⟨[target, next], M',
        afterGas + 51 + arrayCost + indexCost + lengthCost⟩)
      (loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign' harrayLengthOff']
      norm_num [gVerylow]
    case a =>
      rw [hlengthVal, hlengthMem]
      have hg : afterGas + 51 + arrayCost + indexCost + lengthCost - 6 =
          afterGas + 45 + arrayCost + indexCost + lengthCost := by omega
      rw [hg]
      exact harrayTag
  have harrayTail : Func.RunCompiled fs sevm
      (lengthBase.setMach ⟨[next], M',
        afterGas + 57 + arrayCost + indexCost + lengthCost⟩)
      (loadWord targetWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign' htargetOff']
      norm_num [gVerylow]
    case a =>
      rw [htargetVal, htargetMem]
      have hg : afterGas + 57 + arrayCost + indexCost + lengthCost - 6 =
          afterGas + 51 + arrayCost + indexCost + lengthCost := by omega
      rw [hg]
      exact harrayLengthLoad
  have hmemoryCost : arrayLengthMemoryCost M = 6 := by
    simp only [arrayLengthMemoryCost, hsize]
    decide +kernel
  have harithmetic : Func.RunCompiled fs sevm
      (lengthBase.setMach ⟨[length], M,
        afterGas + 72 + arrayLengthMemoryCost M +
          arrayCost + indexCost + lengthCost⟩)
      (pushB256 1 ::: add ::: dup 0 ::: mstoreAt arrayLengthWord +++
        loadWord targetWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    rw [hmemoryCost]
    func_run (5) [next, 6]
    case h_ext => exact Devm.extCost_of_size hsize (by decide +kernel)
    case a =>
      have hg : afterGas + 72 + 6 + arrayCost + indexCost + lengthCost -
          (15 + 6) =
          afterGas + 57 + arrayCost + indexCost + lengthCost := by omega
      rw [hg]
      exact harrayTail
  have hload : Func.RunCompiled fs sevm
      (base.setMach ⟨[arrayLengthSlot], M,
        afterGas + 72 + arrayLengthMemoryCost M +
          arrayCost + indexCost + lengthCost +
          temporalSloadCost sevm base arrayLengthSlot⟩)
      (Ninst.sload ::: pushB256 1 ::: add ::: dup 0 :::
        mstoreAt arrayLengthWord +++ loadWord targetWord +++
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    exact Func.RunCompiled.next
      (temporal_sload_runCompiled hlength (by decide)) harithmetic
  simp only [appendTarget]
  func_run (1)
  case a =>
    have hg : afterGas + 75 + arrayLengthMemoryCost M +
          temporalSloadCost sevm base arrayLengthSlot +
          arrayCost + indexCost + lengthCost - 3 =
        afterGas + 72 + arrayLengthMemoryCost M +
          arrayCost + indexCost + lengthCost +
          temporalSloadCost sevm base arrayLengthSlot := by omega
    rw [hg]
    exact hload

private theorem appendTarget_absentZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (target oldLength next : B256)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (arrayCost indexCost lengthCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (hsize : M.size = 640)
    (hlength : base.getStorVal sevm.currentTarget
      arrayLengthSlot = oldLength)
    (hlengthNext : (1 : B256) + oldLength = next)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = 0)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hindexCost : sstoreValueCost indexOriginal 0 next = indexCost)
    (hlengthCost : sstoreValueCost lengthOriginal oldLength next =
      lengthCost)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal next next =
      movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal next 0 =
      indexClearCost)
    (hwarmArray : (sevm.currentTarget, arrayEntrySlot next) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hsub : next - 1 = oldLength)
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let lengthBase := temporalSloadBase sevm base arrayLengthSlot
    let arrayPost := temporalSstorePost sevm lengthBase
      (arrayEntrySlot next) target
    let indexPost := temporalSstorePost sevm arrayPost
      (indexSlot target) next
    let lengthPost := temporalSstorePost sevm indexPost
      arrayLengthSlot next
    let MAppend := M.write (arrayLengthWord * 32).toNat next.toBytes
    let MIndex := MAppend.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M,
        G + 2540 + temporalSloadCost sevm base arrayLengthSlot +
          arrayCost + indexCost + lengthCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost⟩)
      appendTarget
      (((indexClearPost sevm
          (entryClearPost sevm lengthPost target next)
          target oldLength).addLog eventLog).setMach
        ⟨[next], MLast, G⟩) := by
  dsimp only
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let lengthBase := temporalSloadBase sevm base arrayLengthSlot
  let arrayPost := temporalSstorePost sevm lengthBase arrayKey target
  let indexPost := temporalSstorePost sevm arrayPost indexKey next
  let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
  let MAppend := M.write (arrayLengthWord * 32).toNat next.toBytes
  let imgAppend := Bytes.writeAt img (arrayLengthWord * 32).toNat next.toBytes
  let MIndex := MAppend.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
  have harrayFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 htargetValid.2 hnextBound
  have hlengthFamilies := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 htargetValid.2
  have hlengthArray :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnextNonzero hnextBound
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have harrayPost : lengthPost.getStorVal sevm.currentTarget arrayKey =
      target := by
    rw [temporalSstorePost_other sevm indexPost arrayLengthSlot next
      sevm.currentTarget arrayKey (pairNe (Ne.symm hlengthArray))]
    rw [temporalSstorePost_other sevm arrayPost indexKey next
      sevm.currentTarget arrayKey (pairNe (by
        simpa only [arrayKey, indexKey] using Ne.symm harrayFamilies.2.1))]
    exact temporalSstorePost_self sevm lengthBase arrayKey target
  have hindexPost : lengthPost.getStorVal sevm.currentTarget indexKey =
      next := by
    rw [temporalSstorePost_other sevm indexPost arrayLengthSlot next
      sevm.currentTarget indexKey (pairNe (by
        simpa only [indexKey] using hlengthFamilies.2.1))]
    exact temporalSstorePost_self sevm arrayPost indexKey next
  have hlengthPost : lengthPost.getStorVal sevm.currentTarget
      arrayLengthSlot = next :=
    temporalSstorePost_self sevm indexPost arrayLengthSlot next
  have hwarmArrayPost : (sevm.currentTarget, arrayKey) ∈
      lengthPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm sevm base arrayLengthSlot
      arrayKey hwarmArray
  have hwarmIndexPost : (sevm.currentTarget, indexKey) ∈
      lengthPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm sevm base arrayLengthSlot
      indexKey hwarmIndex
  have hwarmLengthPost : (sevm.currentTarget, arrayLengthSlot) ∈
      lengthPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_warm sevm base arrayLengthSlot
  have hwfAppend : Mem.Wf MAppend := hwf.write _ _
  have hreadsAppend : Mem.Reads MAppend imgAppend :=
    Mem.Reads.write hwf hreads _ _
  have hsizeAppend : MAppend.size = 704 := by
    dsimp only [MAppend]
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide +kernel,
      hsize]
    decide +kernel
  have halignAppend : MAppend.size % 32 = 0 := by rw [hsizeAppend]
  have sliceBefore {word : B256}
      (hbefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat) :
      Bytes.toB256 (imgAppend.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgAppend]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hbefore]
  have htargetAppend : Bytes.toB256
      (imgAppend.sliceD (targetWord * 32).toNat 32 0) = target :=
    (sliceBefore (by decide)).trans htarget
  have hpreviousAppend : Bytes.toB256
      (imgAppend.sliceD (previousPauserWord * 32).toNat 32 0) = 0 :=
    (sliceBefore (by decide)).trans hprevious
  have hnewAppend : Bytes.toB256
      (imgAppend.sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
    (sliceBefore (by decide)).trans hnew
  have hcontinuationAppend : Bytes.toB256
      (imgAppend.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (sliceBefore (by decide)).trans hcontinuation
  have hafter := afterOldPauser_absentZero_runCompiled dp sevm lengthPost
    MAppend imgAppend target oldLength next next arrayOriginal indexOriginal
    lengthOriginal holeCost movedIndexCost tailClearCost lengthRestoreCost
    indexClearCost G hwfAppend hreadsAppend htargetAppend hpreviousAppend
    hnewAppend hcontinuationAppend htargetValid hnextNonzero hnextBound
    hsizeAppend halignAppend harrayPost hindexPost hlengthPost harrayOrig
    hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
    hlengthRestoreCost hindexClearCost hwarmArrayPost hwarmIndexPost
    hwarmLengthPost hsub hgasFinal hstatic
  have hrun := appendTarget_then_runCompiled dp sevm base M img target
    oldLength next arrayOriginal indexOriginal lengthOriginal arrayCost
    indexCost lengthCost
    (G + 2459 + holeCost + movedIndexCost + tailClearCost +
      lengthRestoreCost + indexClearCost)
    (((indexClearPost sevm
        (entryClearPost sevm lengthPost target next)
        target oldLength).addLog eventLog).setMach
      ⟨[next], MLast, G⟩)
    hwf hreads htarget hsize htargetValid hnextNonzero hnextBound hlength
    hlengthNext harray harrayOrig harrayCost hwarmArray hindex hindexOrig
    hindexCost hwarmIndex hlengthOrig hlengthCost (by omega) hstatic hafter
  have hmemoryCost : arrayLengthMemoryCost M = 6 := by
    simp only [arrayLengthMemoryCost, hsize]
    decide +kernel
  have hg : G + 2540 + temporalSloadCost sevm base arrayLengthSlot +
        arrayCost + indexCost + lengthCost + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost =
      G + 2459 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost + 75 +
        arrayLengthMemoryCost M +
        temporalSloadCost sevm base arrayLengthSlot +
        arrayCost + indexCost + lengthCost := by
    rw [hmemoryCost]
    omega
  rw [hg]
  simpa only [lengthPost, indexPost, arrayPost, lengthBase, arrayKey,
    indexKey, MAppend, MIndex, MLength, MLast, eventLog] using hrun

/-- The exact append-then-remove storage model touches no heartbeat-expiry
slot.  This is stated separately so later public wrappers can project the
effect without replaying the write chronology. -/
private theorem appendTarget_absentZero_expiry_unchanged
    (sevm : Sevm) (base : Devm) (target next pauser : B256)
    (htargetValid : canonicalAddress target)
    (hpauserValid : canonicalAddress pauser)
    (hnextBound : next.toNat < 2 ^ 252) :
    let lengthBase := temporalSloadBase sevm base arrayLengthSlot
    let arrayPost := temporalSstorePost sevm lengthBase
      (arrayEntrySlot next) target
    let indexPost := temporalSstorePost sevm arrayPost
      (indexSlot target) next
    let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
    (indexClearPost sevm
        (entryClearPost sevm lengthPost target next)
        target (base.getStorVal sevm.currentTarget arrayLengthSlot)).getStorVal
      sevm.currentTarget (expirySlot pauser) =
    base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  dsimp only
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let expiryKey := expirySlot pauser
  let lengthBase := temporalSloadBase sevm base arrayLengthSlot
  let arrayPost := temporalSstorePost sevm lengthBase arrayKey target
  let indexPost := temporalSstorePost sevm arrayPost indexKey next
  let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
  have hexpiryArray := expirySlot_ne_arrayFamily hpauserValid hnextBound
  have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
    hpauserValid htargetValid htargetValid
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  simp only [indexClearPost, lengthWritePost,
    entryClearPost, indexWritePost, entryWritePost]
  rw [temporalSstorePost_other _ _ (indexSlot target) 0 _ expiryKey
      (pairNe hexpiryRegistry.2.1),
    temporalSstorePost_other _ _ arrayLengthSlot _ _ expiryKey
      (pairNe hexpiryArray.1),
    temporalSstorePost_other _ _ (arrayEntrySlot next) 0 _ expiryKey
      (pairNe hexpiryArray.2),
    temporalSstorePost_other _ _ (indexSlot target) next _ expiryKey
      (pairNe hexpiryRegistry.2.1),
    temporalSstorePost_other _ _ (arrayEntrySlot next) target _ expiryKey
      (pairNe hexpiryArray.2),
    temporalSstorePost_other _ _ arrayLengthSlot next _ expiryKey
      (pairNe hexpiryArray.1),
    temporalSstorePost_other _ _ (indexSlot target) next _ expiryKey
      (pairNe hexpiryRegistry.2.1),
    temporalSstorePost_other _ _ (arrayEntrySlot next) target _ expiryKey
      (pairNe hexpiryArray.2),
    temporalSloadBase_getStorVal]

/-- The exact append-then-remove continuation contributes precisely the
single zero-pauser event; the storage helpers themselves preserve raw logs. -/
private theorem appendTarget_absentZero_logs
    (sevm : Sevm) (base : Devm) (target oldLength next : B256) :
    let lengthBase := temporalSloadBase sevm base arrayLengthSlot
    let arrayPost := temporalSstorePost sevm lengthBase
      (arrayEntrySlot next) target
    let indexPost := temporalSstorePost sevm arrayPost
      (indexSlot target) next
    let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
    ((indexClearPost sevm
        (entryClearPost sevm lengthPost target next)
        target oldLength).addLog eventLog).logs =
      base.logs ++ [eventLog] := by
  dsimp only
  simp only [indexClearPost, lengthWritePost,
    entryClearPost, indexWritePost, entryWritePost]
  have logs_addLog (d : Devm) (log : Log) :
      (d.addLog log).logs = d.logs ++ [log] := rfl
  rw [logs_addLog]
  congr 1
  rw [temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSloadBase_logs]

/-- Exact reserve for the absent-target/zero-pauser kernel.  It includes the
actual assignment and length SLOAD costs and all nine exact SSTORE value-cost
partitions; the fixed component includes the 640→704→736 memory growth. -/
def absentZeroSetPauserKernelGas (sevm : Sevm) (base : Devm)
    (target : B256)
    (assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost : Nat) : Nat :=
  let assigned := assignmentPost sevm base target 0
  2630 + temporalSloadCost sevm base (assignmentSlot target) +
    assignmentCost + temporalSloadCost sevm assigned arrayLengthSlot +
    arrayCost + indexCost + lengthCost + holeCost + movedIndexCost +
    tailClearCost + lengthRestoreCost + indexClearCost

/-- Exact generated-kernel success for an absent target assigned the zero
pauser.  The emitted assignment no-op, append, and removal chronology derives
the unchanged Registry trace/witness, lone `PauserSet`, and preservation of
every canonical expiry slot. -/
theorem setPauserKernel_absentZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (entries : List Entry) (target : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = none)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hsize : M.size = 640)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 0 =
      assignmentCost)
    (harray : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost sevm base target 0).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (assignmentPost sevm base target 0).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1))
      (Nat.toB256 (entries.length + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 (entries.length + 1)) (Nat.toB256 entries.length) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1)) 0 = indexClearCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hsubWord : Nat.toB256 (entries.length + 1) - 1 =
      Nat.toB256 entries.length)
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = entries ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes)) entries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M,
          G + absentZeroSetPauserKernelGas sevm base target assignmentCost
            arrayCost indexCost lengthCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost⟩)
        setPauserKernel post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  let assignmentKey := assignmentSlot target
  let assignBase := assignmentBase sevm base target
  let assignPost := assignmentPost sevm base target 0
  let next := Nat.toB256 (entries.length + 1)
  let oldLength := Nat.toB256 entries.length
  let appendGas := G + 2540 +
    temporalSloadCost sevm assignPost arrayLengthSlot +
    arrayCost + indexCost + lengthCost + holeCost + movedIndexCost +
    tailClearCost + lengthRestoreCost + indexClearCost
  have hassignment : base.getStorVal sevm.currentTarget assignmentKey = 0 := by
    change (Devm.getStor base sevm.currentTarget).get assignmentKey = 0
    simpa [logicalStorageOfStor, assignmentKey,
      findEntry_none_assignmentAt hfind] using
      hw.assignments target htargetValid.2
  have hassignmentBase : assignBase.getStorVal sevm.currentTarget
      assignmentKey = 0 := by
    simpa only [assignBase, assignmentBase,
      temporalSloadBase_getStorVal] using hassignment
  have hwarmAssignment : (sevm.currentTarget, assignmentKey) ∈
      assignBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm base assignmentKey
  have hlength : assignPost.getStorVal sevm.currentTarget
      arrayLengthSlot = oldLength := by
    have hne := registryAddressFamilies_ne_arrayLengthSlot
      htargetValid.2 htargetValid.2
    change (temporalSstorePost sevm assignBase assignmentKey 0).getStorVal
      sevm.currentTarget arrayLengthSlot = oldLength
    rw [temporalSstorePost_other sevm assignBase assignmentKey 0
      sevm.currentTarget arrayLengthSlot (by
        intro hp
        exact hne.1 (congrArg Prod.snd hp).symm)]
    change (temporalSloadBase sevm base assignmentKey).getStorVal
      sevm.currentTarget arrayLengthSlot = oldLength
    rw [temporalSloadBase_getStorVal]
    change (Devm.getStor base sevm.currentTarget).get arrayLengthSlot =
      oldLength
    simpa [logicalStorageOfStor, oldLength] using hw.lengthWord
  have hindex : assignPost.getStorVal sevm.currentTarget
      (indexSlot target) = 0 := by
    have hne := registryAddressFamilies_pairwise
      htargetValid.2 htargetValid.2 htargetValid.2
    change (temporalSstorePost sevm assignBase assignmentKey 0).getStorVal
      sevm.currentTarget (indexSlot target) = 0
    rw [temporalSstorePost_other sevm assignBase assignmentKey 0
      sevm.currentTarget (indexSlot target) (by
        intro hp
        exact hne.1 (congrArg Prod.snd hp).symm)]
    change (temporalSloadBase sevm base assignmentKey).getStorVal
      sevm.currentTarget (indexSlot target) = 0
    rw [temporalSloadBase_getStorVal]
    change (Devm.getStor base sevm.currentTarget).get (indexSlot target) = 0
    change (Devm.getStor base sevm.currentTarget).get (indexSlot target) =
      Nat.toB256 0
    simpa [logicalStorageOfStor, findEntry_none_oneBasedIndexAt hfind] using
      hw.indices target htargetValid.2
  have hnextBound : next.toNat < 2 ^ 252 := by
    dsimp only [next]
    rw [B256.toNat_toB256_of_lt hw.fresh_length_lt_2pow256]
    exact hw.fresh_length_lt_2pow252
  have hnextNonzero : next ≠ 0 := by
    intro hz
    have h := congrArg B256.toNat hz
    rw [show next = Nat.toB256 (entries.length + 1) by rfl,
      B256.toNat_toB256_of_lt hw.fresh_length_lt_2pow256] at h
    simp only [B256.toNat_zero] at h
    omega
  have hlengthNext : (1 : B256) + oldLength = next := by
    simpa only [oldLength, next] using hlengthNextWord
  have hsub : next - 1 = oldLength := by
    simpa only [oldLength, next] using hsubWord
  let M' := M.write (previousPauserWord * 32).toNat (0 : B256).toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          rw [hsize]
          decide))
  have hsize' : M'.size = 640 := by rw [hsizeM', hsize]
  have halign' : M'.size % 32 = 0 := by rw [hsize']
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
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [show 32 = (0 : B256).toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hcontinuation' : Bytes.toB256
      (img'.sliceD (continuationWord * 32).toNat 32 0) = 0 := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      decide)]
    exact hcontinuation
  let lengthBase := temporalSloadBase sevm assignPost arrayLengthSlot
  let arrayPost := temporalSstorePost sevm lengthBase
    (arrayEntrySlot next) target
  let indexPost := temporalSstorePost sevm arrayPost (indexSlot target) next
  let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
  let MAppend := M'.write (arrayLengthWord * 32).toNat next.toBytes
  let MIndex := MAppend.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
  let post := (((indexClearPost sevm
      (entryClearPost sevm lengthPost target next)
      target oldLength).addLog eventLog).setMach ⟨[next], MLast, G⟩)
  have happendRaw := appendTarget_absentZero_runCompiled dp sevm
    assignPost M' img' target oldLength next arrayOriginal indexOriginal
    lengthOriginal arrayCost indexCost lengthCost holeCost movedIndexCost
    tailClearCost lengthRestoreCost indexClearCost G hwf' hreads' htarget'
    hprevious' hnew' hcontinuation' htargetValid hnextNonzero hnextBound
    hsize' hlength hlengthNext harray hindex harrayOrig hindexOrig
    hlengthOrig harrayCost hindexCost hlengthCost hholeCost
    hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    hwarmArray hwarmIndex hsub hgasFinal hstatic
  have happend : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (assignPost.setMach ⟨[], M', appendGas⟩)
      appendTarget post := by
    simpa only [appendGas, post, lengthPost, indexPost, arrayPost, lengthBase,
      MAppend, MIndex, MLength, MLast, eventLog] using happendRaw
  have halign : M.size % 32 = 0 := by rw [hsize]
  have hkernelRun := setPauserKernel_append_runCompiled dp sevm base M img
    post target 0 assignmentOriginal assignmentCost appendGas
    hwf hreads htarget hnew htargetValid (by omega) halign hassignment
    hassignmentOrig hassignmentCost
    (by simp only [appendGas]; norm_num [gCallStipend]; omega) hstatic
    happend
  rcases absentZeroRegistration_sourceTrace_witness hw htargetValid hfind with
    ⟨trace, htrace, hpostEntries, _hwrites, hwpost⟩
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, rfl, ?_, ?_⟩
  · have hg : G + absentZeroSetPauserKernelGas sevm base target
          assignmentCost arrayCost indexCost lengthCost holeCost
          movedIndexCost tailClearCost lengthRestoreCost indexClearCost =
        appendGas + appendSetPauserKernelPrefixGas sevm base target
          assignmentCost := by
      dsimp only [absentZeroSetPauserKernelGas,
        appendSetPauserKernelPrefixGas, appendGas, assignPost,
        assignBase, assignmentKey, assignmentPost,
        assignmentBase]
      omega
    rw [hg]
    exact hkernelRun
  · dsimp only [post]
    have hlogs := appendTarget_absentZero_logs sevm assignPost target
      oldLength next
    dsimp only [lengthPost, indexPost, arrayPost, lengthBase, eventLog] at hlogs
    have logs_setMach (d : Devm) (mach : Mach) :
        (d.setMach mach).logs = d.logs := rfl
    rw [logs_setMach, hlogs]
    dsimp only [assignPost, assignmentPost, assignmentBase]
    rw [temporalSstorePost_logs, temporalSloadBase_logs]
  · intro pauser hpauser
    have hexp := appendTarget_absentZero_expiry_unchanged sevm assignPost
      target next pauser htargetValid.2 hpauser hnextBound
    dsimp only [lengthPost, indexPost, arrayPost, lengthBase] at hexp
    rw [hlength] at hexp
    have hne := expirySlot_ne_registryAddressFamilies hpauser
      htargetValid.2 htargetValid.2
    have hassignmentExpiry : assignPost.getStorVal sevm.currentTarget
        (expirySlot pauser) =
        base.getStorVal sevm.currentTarget (expirySlot pauser) := by
      change (temporalSstorePost sevm assignBase assignmentKey 0).getStorVal
        sevm.currentTarget (expirySlot pauser) = _
      rw [temporalSstorePost_other sevm assignBase assignmentKey 0
        sevm.currentTarget (expirySlot pauser) (by
          intro hp
          exact hne.1 (congrArg Prod.snd hp))]
      dsimp only [assignBase, assignmentBase]
      rw [temporalSloadBase_getStorVal]
    calc
      post.getStorVal sevm.currentTarget (expirySlot pauser) =
          (indexClearPost sevm
            (entryClearPost sevm lengthPost target next)
            target oldLength).getStorVal sevm.currentTarget
              (expirySlot pauser) := rfl
      _ = assignPost.getStorVal sevm.currentTarget
          (expirySlot pauser) := hexp
      _ = base.getStorVal sevm.currentTarget
          (expirySlot pauser) := hassignmentExpiry

private theorem absentCanonicalAddressArgs_success_runCompiled
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {G : Nat} {body : Func} {post : Devm} {target : B256}
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (htargetMask : addressMask &&& target = 0)
    (hnewMask : addressMask &&& (0 : B256) = 0)
    (hbody : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) body post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 66⟩)
      (canonicalAddressArg 0 (canonicalAddressArg 1 body)) post := by
  have checkNonAddressRun
      (checked : B256) (tail : Func) (G' : Nat)
      (hmask : addressMask &&& checked = 0)
      (htail : Func.RunCompiled
        ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty, G'⟩) tail post) :
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨checked :: [], Mem.empty, G' + 27⟩)
        (checkNonAddress +++ ((.call emptyRevertSlot) <?> tail)) post := by
    have hbranch : Func.RunCompiled
        ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach
          ⟨addressMask :: checked :: [], Mem.empty, G' + 16⟩)
        ([Ninst.and] +++ ((.call emptyRevertSlot) <?> tail)) post := by
      func_run (2) [0]
      case h_arm =>
        have hg : G' + 16 - 16 = G' := by omega
        rw [hg]
        exact htail
    have hshiftRaw : Func.RunCompiled
        ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach
          ⟨((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) :: checked :: [],
            Mem.empty, G' + 16⟩)
        ([Ninst.and] +++ ((.call emptyRevertSlot) <?> tail)) post := by
      rw [← addressMask_eq_shl]
      exact hbranch
    have hshift : Func.RunCompiled
        ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach
          ⟨~~~(0 : B256) :: checked :: [], Mem.empty, G' + 16 + 6⟩)
        ([pushB256 (Nat.toB256 160), shl] +++
          ([Ninst.and] +++ ((.call emptyRevertSlot) <?> tail))) post := by
      func_run (2)
        [((~~~(0 : B256)) <<< (Nat.toB256 160).toNat)]
      case a => exact hshiftRaw
    have hnot : Func.RunCompiled
        ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨checked :: [], Mem.empty, G' + 16 + 6 + 5⟩)
        ([pushB256 0, not] +++
          ([pushB256 (Nat.toB256 160), shl] +++
            ([Ninst.and] +++ ((.call emptyRevertSlot) <?> tail)))) post := by
      func_run (2) [~~~(0 : B256)]
      case a => exact hshift
    have hg : G' + 16 + 6 + 5 = G' + 27 := by omega
    have hsplit :
        checkNonAddress +++ ((.call emptyRevertSlot) <?> tail) =
          [pushB256 0, not] +++
            ([pushB256 (Nat.toB256 160), shl] +++
              ([Ninst.and] +++ ((.call emptyRevertSlot) <?> tail))) := by
      rfl
    rw [← hg, hsplit]
    exact hnot
  have hnewCheck := checkNonAddressRun 0 body G hnewMask hbody
  have hnewArg : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 27 + 6⟩)
      (arg 1 +++ checkNonAddress +++
        ((.call emptyRevertSlot) <?> body)) post := by
    unfold arg cdl
    func_run (2)
    case a => rw [hargNew]; exact hnewCheck
  have hnewRun : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 33⟩)
      (canonicalAddressArg 1 body) post := by
    have hg : G + 27 + 6 = G + 33 := by omega
    have hsplit :
        canonicalAddressArg 1 body =
          arg 1 +++ checkNonAddress +++
            ((.call emptyRevertSlot) <?> body) := by
      rfl
    rw [← hg, hsplit]
    exact hnewArg
  have htargetCheck := checkNonAddressRun target
    (canonicalAddressArg 1 body) (G + 33) htargetMask hnewRun
  have htargetArg : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 33 + 27 + 6⟩)
      (arg 0 +++ checkNonAddress +++
        ((.call emptyRevertSlot) <?> canonicalAddressArg 1 body)) post := by
    unfold arg cdl
    func_run (2)
    case a => rw [hargTarget]; exact htargetCheck
  have htargetRun : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 33 + 33⟩)
      (canonicalAddressArg 0 (canonicalAddressArg 1 body)) post := by
    have hg : G + 33 + 27 + 6 = G + 33 + 33 := by omega
    have hsplit :
        canonicalAddressArg 0 (canonicalAddressArg 1 body) =
          arg 0 +++ checkNonAddress +++
            ((.call emptyRevertSlot) <?> canonicalAddressArg 1 body) := by
      rfl
    rw [← hg, hsplit]
    exact htargetArg
  have hg : G + 33 + 33 = G + 66 := by omega
  rw [← hg]
  exact htargetRun

private theorem absentZeroRegisterPauserBody_fromStage_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base post : Devm)
    (target : B256) (bodyGas stageGas : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (htargetMask : addressMask &&& target = 0)
    (hnewMask : addressMask &&& (0 : B256) = 0)
    (hgas : bodyGas = stageGas + 109)
    (hstage : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, stageGas⟩)
      (arg 0 +++ mstoreAt targetWord +++
        arg 1 +++ mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 0 ::: mstoreAt continuationWord +++
        .call setPauserSlot) post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, bodyGas⟩)
      (registerPauser dp) post := by
  have hadminRun : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty, stageGas + 22⟩)
      (onlyAdmin dp
        (arg 0 +++ mstoreAt targetWord +++
          arg 1 +++ mstoreAt newPauserWord +++
          pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 0 ::: mstoreAt continuationWord +++
          .call setPauserSlot)) post := by
    unfold onlyAdmin pushDeployWord
    func_run (4) [1]
    case h_val => simp [hadmin, B256.eqCheck]
    case h_arm => simpa using hstage
  have htargetRun := absentCanonicalAddressArgs_success_runCompiled
    hargTarget hargNew htargetMask hnewMask hadminRun
  have hstaticRun : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach
        ⟨[], Mem.empty, stageGas + 22 + 33 + 33 + 21⟩)
      (requireStaticArgs 2
        (canonicalAddressArg 0
          (canonicalAddressArg 1
            (onlyAdmin dp
              (arg 0 +++ mstoreAt targetWord +++
                arg 1 +++ mstoreAt newPauserWord +++
                pushB256 0 ::: mstoreAt previousPauserWord +++
                pushB256 0 ::: mstoreAt continuationWord +++
                .call setPauserSlot))))) post := by
    unfold requireStaticArgs
    func_run (4) [0]
    case h_arm =>
      have hgstatic :
          stageGas + 22 + 33 + 33 + 21 - 21 =
            stageGas + 22 + 33 + 33 := by
        omega
      rw [hgstatic]
      exact htargetRun
  have hg : ((((stageGas + 22) + 33) + 33) + 21) = bodyGas := by
    omega
  rw [← hg]
  simpa only [registerPauser] using hstaticRun

/-- Exact production-body reserve for absent-target/zero-pauser registration. -/
def absentZeroRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target : B256)
    (assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost : Nat) : Nat :=
  221 + absentZeroSetPauserKernelGas sevm base target assignmentCost arrayCost
    indexCost lengthCost holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost

/-- Exact successful production body for absent-target/zero-pauser
registration. -/
theorem registerPauser_body_absentZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = none)
    (htargetValid : nonzeroCanonicalAddress target)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 0 =
      assignmentCost)
    (harray : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost sevm base target 0).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (assignmentPost sevm base target 0).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1))
      (Nat.toB256 (entries.length + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 (entries.length + 1)) (Nat.toB256 entries.length) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1)) 0 = indexClearCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hsubWord : Nat.toB256 (entries.length + 1) - 1 =
      Nat.toB256 entries.length)
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = entries ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes)) entries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + absentZeroRegisterBodyGas sevm base target assignmentCost
            arrayCost indexCost lengthCost holeCost movedIndexCost
            tailClearCost lengthRestoreCost indexClearCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser) := by
  let M := registerMemory target 0
  let img := registerImage target 0
  rcases registerMemory_spec target 0 with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      _hpreviousRead, hcontinuationRead⟩
  rcases setPauserKernel_absentZero_runCompiled dp sevm base M img entries
      target assignmentOriginal arrayOriginal indexOriginal lengthOriginal
      assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost G hw hfind hwf hreads
      htargetRead hnewRead hcontinuationRead htargetValid hsize
      hassignmentOrig hassignmentCost harray harrayOrig harrayCost hwarmArray
      hindexOrig hindexCost hwarmIndex hlengthOrig hlengthCost hholeCost
      hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
      hlengthNextWord hsubWord hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hkernel, hgas, hlogs,
      hexpiries⟩
  have hstage := registerPauser_stageArgs_runCompiled dp sevm base target 0
    (G + absentZeroSetPauserKernelGas sevm base target assignmentCost
      arrayCost indexCost lengthCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost)
    _ hargTarget hargNew hkernel
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, hgas, hlogs,
    hexpiries⟩
  have htargetMask := canonicalAddress_mask_zero htargetValid.2
  have hnewMask : addressMask &&& (0 : B256) = 0 := by decide +kernel
  apply absentZeroRegisterPauserBody_fromStage_runCompiled dp sevm base post
    target
    (G + absentZeroRegisterBodyGas sevm base target assignmentCost arrayCost
      indexCost lengthCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost)
    (G + absentZeroSetPauserKernelGas sevm base target assignmentCost
      arrayCost indexCost lengthCost holeCost movedIndexCost tailClearCost
      lengthRestoreCost indexClearCost + 112)
    hdata hadmin hargTarget hargNew htargetMask hnewMask
  · simp only [absentZeroRegisterBodyGas]
    omega
  · exact hstage

/-- Exact generated-runtime success for absent-target/zero-pauser
registration. -/
theorem registerPauser_runCompiledTo_absentZero
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost G : Nat)
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
    (hfind : findEntry entries target = none)
    (htargetValid : nonzeroCanonicalAddress target)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 0 =
      assignmentCost)
    (harray : (assignmentPost sevm base target 0).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost sevm base target 0).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (assignmentPost sevm base target 0).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1))
      (Nat.toB256 (entries.length + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 (entries.length + 1)) (Nat.toB256 entries.length) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1)) 0 = indexClearCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hsubWord : Nat.toB256 (entries.length + 1) - 1 =
      Nat.toB256 entries.length)
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    ∃ trace post,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = entries ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes)) entries ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            absentZeroRegisterBodyGas sevm base target assignmentCost
              arrayCost indexCost lengthCost holeCost movedIndexCost
              tailClearCost lengthRestoreCost indexClearCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩] ∧
      (∀ pauser, canonicalAddress pauser →
        post.getStorVal sevm.currentTarget (expirySlot pauser) =
          base.getStorVal sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_absentZero_runCompiled dp sevm base entries target
      assignmentOriginal arrayOriginal indexOriginal lengthOriginal
      assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost G hbodyData hadmin
      hargTarget hargNew hw hfind htargetValid hassignmentOrig hassignmentCost
      harray harrayOrig harrayCost hwarmArray hindexOrig hindexCost hwarmIndex
      hlengthOrig hlengthCost hholeCost hmovedIndexCost htailClearCost
      hlengthRestoreCost hindexClearCost hlengthNextWord hsubWord hgasFinal
      hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hbody, hgas, hlogs,
      hexpiries⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (absentZeroRegisterBodyGas sevm base target assignmentCost arrayCost
        indexCost lengthCost holeCost movedIndexCost tailClearCost
        lengthRestoreCost indexClearCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
    hexpiries, hcompile⟩

/-- Exact clean direct-message effects for absent-target/zero-pauser
registration, derived from the generated-runtime execution. -/
theorem registerPauser_absentZero_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr} {final settled : Devm}
    (entries : List Entry) (target : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target 0)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      absentZeroRegisterBodyGas (initSevm msg) (initDevm msg) target
        assignmentCost arrayCost indexCost lengthCost holeCost movedIndexCost
        tailClearCost lengthRestoreCost indexClearCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor (initDevm msg) ca)) entries)
    (hfind : findEntry entries target = none)
    (htargetValid : nonzeroCanonicalAddress target)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 0 =
      assignmentCost)
    (harray : (assignmentPost (initSevm msg) (initDevm msg)
      target 0).getStorVal ca
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (ca,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost (initSevm msg) (initDevm msg)
          target 0).accessedStorageKeys)
    (hindexOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (ca, indexSlot target) ∈
      (assignmentPost (initSevm msg) (initDevm msg)
        target 0).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal (initSevm msg) ca arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1))
      (Nat.toB256 (entries.length + 1)) = movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal
      (Nat.toB256 (entries.length + 1)) (Nat.toB256 entries.length) =
        lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal
      (Nat.toB256 (entries.length + 1)) 0 = indexClearCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hsubWord : Nat.toB256 (entries.length + 1) - 1 =
      Nat.toB256 entries.length)
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : (initSevm msg).isStatic = false)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    ∃ trace,
      setPauserSourceTrace entries target 0 = some trace ∧
      trace.postEntries = entries ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor (initDevm msg) ca) trace.writes)) entries ∧
      settled.gasLeft = G ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, 0, 0], []⟩] ∧
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
  rcases registerPauser_runCompiledTo_absentZero dp (initSevm msg)
      (initDevm msg) entries target assignmentOriginal arrayOriginal
      indexOriginal lengthOriginal assignmentCost arrayCost indexCost
      lengthCost holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost G hdataLength hvalueInit hselector hcodeAddressInit
      hcodeInit hadminInit hargTarget hargNew
      (by simpa [hownerInit] using hw) hfind htargetValid
      (by simpa [hownerInit] using hassignmentOrig) hassignmentCost
      (by simpa [hownerInit] using harray)
      (by simpa [hownerInit] using harrayOrig) harrayCost
      (by simpa [hownerInit] using hwarmArray)
      (by simpa [hownerInit] using hindexOrig) hindexCost
      (by simpa [hownerInit] using hwarmIndex)
      (by simpa [hownerInit] using hlengthOrig) hlengthCost hholeCost
      hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
      hlengthNextWord hsubWord hgasFinal hstatic with
    ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas, hlogs,
      hexpiries, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          absentZeroRegisterBodyGas (initSevm msg) (initDevm msg) target
            assignmentCost arrayCost indexCost lengthCost holeCost
            movedIndexCost tailClearCost lengthRestoreCost indexClearCost⟩ =
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
