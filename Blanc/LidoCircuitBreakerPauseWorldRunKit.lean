import Blanc.LidoCircuitBreakerPauseSuffixWalk

/-!
Composition kit for the pause witness-world runs.

`Blanc/LidoCircuitBreakerPauseWorldRun.lean` composes the complete `.ok`
`pause(address)` walks at the two witness worlds of
`Blanc/LidoCircuitBreakerPauseWorld.lean`.  Two of the landed legs cannot be
consumed there directly, and this leaf carries the bridging material:

* **Cold-entry `removeTarget` walks.**  The register-side
  `removeTarget_toFinish_runCompiled` family charges its three array-region
  `SLOAD`s warm and demands the three keys warm at entry — true at the
  unregister world, whose message pre-warms them, but false on the pause path:
  the pause worlds enter with empty accessed sets, and nothing between message
  entry and `removeTarget` touches the array region.  The
  `…_coldEntry_runCompiled` variants below restate the same walks in the
  temporal convention: the three `SLOAD` charges are hypothesis-supplied
  `temporalSloadCost` equations and the walk threads the warmed
  `temporalSloadBase` successors, so the store suffix runs at a state where
  the keys really are warm.  The private store-suffix lemmas they consume are
  file-scoped in `Blanc/LidoCircuitBreakerRegistrySubstrate.lean` and are
  transcribed here verbatim; they belong upstream, and should be deduplicated
  there the next time that file is opened.

* **An existential `pauseAfterSet` leg.**  `pauseAfterSet_toSuccess_runCompiled`
  fixes its final state `post` *before* quantifying over the `pauseSuccess`
  boundary state `mid`.  Because the boundary facts pin `mid` only up to
  membership-extensionality of its accessed sets, distinct conforming `mid`s
  exist and a deterministic continuation walk cannot reach one fixed `post`
  from all of them — the continuation premise is unsatisfiable and the leg
  cannot be applied.  `pauseAfterSet_toSuccess_exists_runCompiled` below
  proves the same walk with the boundary state exported existentially: the
  consumer receives the one actual `mid`, its projection facts, and a closure
  extending any continuation walk from that `mid` to the full `pauseAfterSet`
  walk.

* **Seam transports.**  The crossings pin the boundary state's world as a
  zero-value `subBal`/`addBal` chain; `seam_getStorVal` collapses that chain
  on storage projections, in the style of `Weth10HolderFlowResult.lean`'s
  `state_addBal_getStor_eq`.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Verbatim transcriptions from the Registry substrate

The three store-suffix lemmas below are word-for-word copies of the private
`pushZero_targetIndexKey_prepend_runCompiled`,
`removeTarget_restoreTail_runCompiled` and
`removeTarget_storePrefix_runCompiled` in
`Blanc/LidoCircuitBreakerRegistrySubstrate.lean`, which this module cannot
name.  Keep them in sync with the originals; the right long-term home is the
substrate. -/

private theorem pushZero_targetIndexKey_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {target : B256} {stack : List B256} {G : Nat}
    {tail : Func} {post : Devm}
    (hvalue : (M.read (targetWord * 32).toNat 32).1.toB256 = target)
    (hmemory : (M.read (targetWord * 32).toNat 32).2 = M)
    (halign : M.size % 32 = 0)
    (hcovered : (targetWord * 32).toNat + 32 ≤ M.size)
    (hroom : stack.length < 1021)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨indexSlot target :: 0 :: stack, M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 14⟩)
      (pushB256 0 ::: targetIndexKey +++ tail) post := by
  have htag : Func.RunCompiled fs sevm
      (base.setMach ⟨target :: 0 :: stack, M, G + 6⟩)
      (tagTop indexRegion +++ tail) post := by
    func_run (2) [indexSlot target]
    case a =>
      have hg : G + 6 - 6 = G := by omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (base.setMach ⟨indexSlot target :: 0 :: stack, M, G⟩) tail post
      exact htail
    all_goals simp only [Devm.stack_setMach, List.length_cons]
    all_goals omega
  have hload : Func.RunCompiled fs sevm
      (base.setMach ⟨0 :: stack, M, G + 12⟩)
      (loadWord targetWord +++ tagTop indexRegion +++ tail) post := by
    exact targetWord_prepend_runCompiled hvalue hmemory halign hcovered
      (by simp only [List.length_cons]; omega) htag
  have hload' : Func.RunCompiled fs sevm
      (base.setMach ⟨0 :: stack, M, G + 12⟩)
      (targetIndexKey +++ tail) post := by
    simpa only [targetIndexKey, prepend_append] using hload
  apply Func.RunCompiled.next
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm)
        (devm := base.setMach ⟨stack, M, G + 14⟩)
        (w := 0) (c := gBase) (G := G + 12) rfl
        (by simp only [Devm.gasLeft_setMach]; norm_num [gBase])
        (by simp only [Devm.stack_setMach]; omega))
  · exact hload'


set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem removeTarget_restoreTail_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength lengthValue indexValue _previous : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (lengthOriginal indexOriginal : B256)
    (lengthRestoreCost indexClearCost finishGas G : Nat)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hlengthWord : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = lengthValue)
    (htargetValid : nonzeroCanonicalAddress target)
    (hsize : 736 ≤ M.size) (halign : M.size % 32 = 0)
    (hlength : base.getStorVal sevm.currentTarget
      arrayLengthSlot = lengthValue)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = indexValue)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal lengthValue oldLength =
      lengthRestoreCost)
    (hindexCost : sstoreValueCost indexOriginal indexValue 0 = indexClearCost)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hsub : lengthValue - 1 = oldLength)
    (hgasFinal : gCallStipend < G + finishGas + 12 + indexClearCost)
    (hstatic : sevm.isStatic = false)
    (post : Devm)
    (hfinish :
      let removePost := indexClearPost sevm base target oldLength
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, M, G + finishGas⟩)
        finishSetPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 44 + indexClearCost + lengthRestoreCost⟩)
      (loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
  let indexKey := indexSlot target
  let lengthPost := lengthWritePost sevm base oldLength
  let removePost := indexClearPost sevm base target oldLength
  have hlengthFamilies := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 htargetValid.2
  have hindexLength : indexKey ≠ arrayLengthSlot := by
    simpa only [indexKey] using hlengthFamilies.2.1
  have hindexPost : lengthPost.getStorVal sevm.currentTarget
      indexKey = indexValue := by
    rw [show lengthPost = temporalSstorePost sevm base
      arrayLengthSlot oldLength by rfl]
    rw [temporalSstorePost_other sevm base arrayLengthSlot oldLength
      sevm.currentTarget indexKey (by
        intro hp
        exact hindexLength (congrArg Prod.snd hp))]
    exact hindex
  have hwarmIndexPost : (sevm.currentTarget, indexKey) ∈
      lengthPost.accessedStorageKeys := by
    rw [show lengthPost = temporalSstorePost sevm base
      arrayLengthSlot oldLength by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmIndex
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 736 := by decide
    omega
  have hlengthCovered : (arrayLengthWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 736 := by decide
    omega
  have htargetMemory : (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have hlengthMemory :
      (M.read (arrayLengthWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hlengthCovered)]
  have htargetValue :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  have hlengthValue :
      (M.read (arrayLengthWord * 32).toNat 32).1.toB256 = lengthValue := by
    rw [Mem.Reads.read hreads]
    exact hlengthWord
  let fs := (runtime dp).main :: (runtime dp).aux
  have hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser := by
    simp [fs, runtime, aux, finishSetPauserSlot]
  have hfinishCall : Func.RunCompiled fs sevm
      (removePost.setMach ⟨stack, M, G + finishGas + 12⟩)
      (.call finishSetPauserSlot)
      post := by
    apply Func.RunCompiled.call hfinishLookup (by
      simp only [Devm.stack_setMach]
      omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := removePost.setMach
            ⟨stack, M, G + finishGas + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G + finishGas)
          (by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gMid, gJumpdest]))
    · simpa only [fs] using hfinish
  have hstoreIndex : Func.RunCompiled fs sevm
      (lengthPost.setMach
        ⟨indexKey :: 0 :: stack, M,
          G + finishGas + 12 + indexClearCost⟩)
      (Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    have hsstore : Ninst.RunCompiled sevm
        (lengthPost.setMach
          ⟨indexKey :: 0 :: stack, M,
            G + finishGas + 12 + indexClearCost⟩)
        Ninst.sstore
        (removePost.setMach ⟨stack, M, G + finishGas + 12⟩) := by
      exact temporal_sstore_runCompiled hindexPost hindexOrig hindexCost
        hwarmIndexPost hgasFinal hstatic
    exact Func.RunCompiled.next hsstore hfinishCall
  have hindexTail : Func.RunCompiled fs sevm
      (lengthPost.setMach
        ⟨stack, M, G + finishGas + 26 + indexClearCost⟩)
      (pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    have htail := hstoreIndex
    simp only [indexKey] at htail
    have hrun := pushZero_targetIndexKey_prepend_runCompiled htargetValue
      htargetMemory halign htargetCovered (by omega) htail
    have hg : G + finishGas + 12 + indexClearCost + 14 =
        G + finishGas + 26 + indexClearCost := by omega
    rw [hg] at hrun
    exact hrun
  have hstoreLength : Func.RunCompiled fs sevm
      (base.setMach
          ⟨arrayLengthSlot :: oldLength :: stack, M,
          G + finishGas + 26 + indexClearCost + lengthRestoreCost⟩)
      (Ninst.sstore ::: pushB256 0 ::: targetIndexKey +++
        Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    have hsstore : Ninst.RunCompiled sevm
        (base.setMach
          ⟨arrayLengthSlot :: oldLength :: stack, M,
            G + finishGas + 26 + indexClearCost + lengthRestoreCost⟩)
        Ninst.sstore
        (lengthPost.setMach
          ⟨stack, M, G + finishGas + 26 + indexClearCost⟩) := by
      exact temporal_sstore_runCompiled hlength hlengthOrig hlengthCost
        hwarmLength (lt_of_lt_of_le hgasFinal (by omega)) hstatic
    exact Func.RunCompiled.next hsstore hindexTail
  func_run (6) [3]
  all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hlengthCovered]
    norm_num [gVerylow]
  case a =>
    rw [hlengthValue, hlengthMemory]
    change Func.RunCompiled _ _
      (base.setMach
        ⟨arrayLengthSlot :: (lengthValue - 1) :: stack, M,
          G + finishGas + 44 + indexClearCost + lengthRestoreCost - 18⟩)
      _ _
    rw [hsub]
    have hg : G + finishGas + 44 + indexClearCost + lengthRestoreCost - 18 =
        G + finishGas + 26 + indexClearCost + lengthRestoreCost := by omega
    rw [hg]
    exact hstoreLength

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem removeTarget_storePrefix_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next : B256) (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost finishGas G : Nat)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hremovedWord : Bytes.toB256
      (img.sliceD (removedIndexWord * 32).toNat 32 0) = next)
    (hlengthWord : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = next)
    (hlastWord : Bytes.toB256
      (img.sliceD (lastTargetWord * 32).toNat 32 0) = target)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (hsize : 736 ≤ M.size) (halign : M.size % 32 = 0)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlength : base.getStorVal sevm.currentTarget
      arrayLengthSlot = next)
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
    (hgasFinal : gCallStipend < G + finishGas + 12 + indexClearCost)
    (hstatic : sevm.isStatic = false)
    (post : Devm)
    (hfinish :
      let tailPost := entryClearPost sevm base target next
      let removePost := indexClearPost sevm tailPost target oldLength
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, M, G + finishGas⟩)
        finishSetPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 94 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost⟩)
      (loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++
        Ninst.sstore ::: pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let holePost := entryWritePost sevm base target next
  let movedPost := indexWritePost sevm base target next
  let tailPost := entryClearPost sevm base target next
  have hlengthArray : arrayLengthSlot ≠ arrayKey := by
    simpa only [arrayKey] using
      arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnextNonzero hnextBound
  have hindexArray : indexKey ≠ arrayKey := by
    simpa only [indexKey, arrayKey] using
      (registryAddressFamilies_ne_arrayEntrySlot
        htargetValid.2 htargetValid.2 hnextBound).2.1
  have hindexLength : indexKey ≠ arrayLengthSlot := by
    simpa only [indexKey] using
      (registryAddressFamilies_ne_arrayLengthSlot
        htargetValid.2 htargetValid.2).2.1
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have harrayHole : holePost.getStorVal sevm.currentTarget arrayKey =
      target := by
    simpa only [holePost, entryWritePost, arrayKey] using
      temporalSstorePost_self sevm base (arrayEntrySlot next) target
  have hindexHole : holePost.getStorVal sevm.currentTarget indexKey =
      next := by
    rw [show holePost = temporalSstorePost sevm base arrayKey target by rfl]
    rw [temporalSstorePost_other sevm base arrayKey target
      sevm.currentTarget indexKey (pairNe hindexArray)]
    exact hindex
  have hlengthHole : holePost.getStorVal sevm.currentTarget
      arrayLengthSlot = next := by
    rw [show holePost = temporalSstorePost sevm base arrayKey target by rfl]
    rw [temporalSstorePost_other sevm base arrayKey target
      sevm.currentTarget arrayLengthSlot (pairNe hlengthArray)]
    exact hlength
  have harrayMoved : movedPost.getStorVal sevm.currentTarget arrayKey =
      target := by
    rw [show movedPost = temporalSstorePost sevm holePost
      indexKey next by rfl]
    rw [temporalSstorePost_other sevm holePost indexKey next
      sevm.currentTarget arrayKey (pairNe hindexArray.symm)]
    exact harrayHole
  have hindexMoved : movedPost.getStorVal sevm.currentTarget indexKey =
      next := by
    simpa only [movedPost, indexWritePost, indexKey,
      holePost, entryWritePost] using
      temporalSstorePost_self sevm holePost indexKey next
  have hlengthMoved : movedPost.getStorVal sevm.currentTarget
      arrayLengthSlot = next := by
    rw [show movedPost = temporalSstorePost sevm holePost
      indexKey next by rfl]
    rw [temporalSstorePost_other sevm holePost indexKey next
      sevm.currentTarget arrayLengthSlot (pairNe hindexLength.symm)]
    exact hlengthHole
  have hlengthTail : tailPost.getStorVal sevm.currentTarget
      arrayLengthSlot = next := by
    rw [show tailPost = temporalSstorePost sevm movedPost
      arrayKey 0 by rfl]
    rw [temporalSstorePost_other sevm movedPost arrayKey 0
      sevm.currentTarget arrayLengthSlot (pairNe hlengthArray)]
    exact hlengthMoved
  have hindexTail : tailPost.getStorVal sevm.currentTarget indexKey =
      next := by
    rw [show tailPost = temporalSstorePost sevm movedPost
      arrayKey 0 by rfl]
    rw [temporalSstorePost_other sevm movedPost arrayKey 0
      sevm.currentTarget indexKey (pairNe hindexArray)]
    exact hindexMoved
  have hwarmArrayHole : (sevm.currentTarget, arrayKey) ∈
      holePost.accessedStorageKeys := by
    rw [show holePost = temporalSstorePost sevm base arrayKey target by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmArray
  have hwarmIndexHole : (sevm.currentTarget, indexKey) ∈
      holePost.accessedStorageKeys := by
    rw [show holePost = temporalSstorePost sevm base arrayKey target by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmIndex
  have hwarmArrayMoved : (sevm.currentTarget, arrayKey) ∈
      movedPost.accessedStorageKeys := by
    rw [show movedPost = temporalSstorePost sevm holePost indexKey next by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmArrayHole
  have hwarmIndexTail : (sevm.currentTarget, indexKey) ∈
      tailPost.accessedStorageKeys := by
    rw [show tailPost = temporalSstorePost sevm movedPost arrayKey 0 by rfl,
      temporalSstorePost_accessedStorageKeys,
      show movedPost = temporalSstorePost sevm holePost indexKey next by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmIndexHole
  have hwarmLengthTail : (sevm.currentTarget, arrayLengthSlot) ∈
      tailPost.accessedStorageKeys := by
    rw [show tailPost = temporalSstorePost sevm movedPost arrayKey 0 by rfl,
      temporalSstorePost_accessedStorageKeys,
      show movedPost = temporalSstorePost sevm holePost indexKey next by rfl,
      temporalSstorePost_accessedStorageKeys,
      show holePost = temporalSstorePost sevm base arrayKey target by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmLength
  have covered (word : B256)
      (hoff : (word * 32).toNat + 32 ≤ 736) :
      (word * 32).toNat + 32 ≤ M.size := by omega
  have readMemory (word : B256)
      (hoff : (word * 32).toNat + 32 ≤ 736) :
      (M.read (word * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign (covered word hoff))]
  have readValue (word value : B256)
      (hvalue : Bytes.toB256
        (img.sliceD (word * 32).toNat 32 0) = value) :
      (M.read (word * 32).toNat 32).1.toB256 = value := by
    rw [Mem.Reads.read hreads]
    exact hvalue
  have htargetMemory := readMemory targetWord (by decide)
  have hremovedMemory := readMemory removedIndexWord (by decide)
  have hlengthMemory := readMemory arrayLengthWord (by decide)
  have hlastMemory := readMemory lastTargetWord (by decide)
  have htargetValue := readValue targetWord target htarget
  have hremovedValue := readValue removedIndexWord next hremovedWord
  have hlengthValue := readValue arrayLengthWord next hlengthWord
  have hlastValue := readValue lastTargetWord target hlastWord
  have hrestore := removeTarget_restoreTail_runCompiled
    dp sevm tailPost M img target oldLength next next 0 stack hstack
    lengthOriginal indexOriginal lengthRestoreCost indexClearCost finishGas G
    hreads htarget hlengthWord htargetValid hsize halign hlengthTail hindexTail
    hlengthOrig hindexOrig hlengthRestoreCost hindexClearCost hwarmLengthTail
    hwarmIndexTail hsub hgasFinal hstatic post
    (by simpa only [tailPost] using hfinish)
  let fs := (runtime dp).main :: (runtime dp).aux
  have hrestore' : Func.RunCompiled fs sevm
      (tailPost.setMach
        ⟨stack, M,
          G + finishGas + 44 + lengthRestoreCost + indexClearCost⟩)
      (loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    have hg : G + finishGas + 44 + lengthRestoreCost + indexClearCost =
        G + finishGas + 44 + indexClearCost + lengthRestoreCost := by omega
    rw [hg]
    simpa only [fs, tailPost] using hrestore
  have hstoreTail : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨arrayKey :: 0 :: stack, M,
          G + finishGas + 44 + lengthRestoreCost + indexClearCost +
            tailClearCost⟩)
      (Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled harrayMoved harrayOrig htailClearCost
        hwarmArrayMoved (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      hrestore'
  have htailTag : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨next :: 0 :: stack, M,
          G + finishGas + 50 + lengthRestoreCost + indexClearCost +
            tailClearCost⟩)
      (tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [arrayKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 50 + lengthRestoreCost + indexClearCost +
          tailClearCost - 6 =
          G + finishGas + 44 + lengthRestoreCost + indexClearCost +
            tailClearCost := by omega
      rw [hg]
      exact hstoreTail
  have htailLength : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨0 :: stack, M,
          G + finishGas + 56 + lengthRestoreCost + indexClearCost +
            tailClearCost⟩)
      (loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (2) [3]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered arrayLengthWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlengthValue, hlengthMemory]
      have hg : G + finishGas + 56 + lengthRestoreCost + indexClearCost +
          tailClearCost - 6 =
          G + finishGas + 50 + lengthRestoreCost + indexClearCost +
            tailClearCost := by omega
      rw [hg]
      exact htailTag
  have htailPrefix : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨stack, M,
          G + finishGas + 58 + lengthRestoreCost + indexClearCost +
            tailClearCost⟩)
      (pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (1)
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case a =>
      have hg : G + finishGas + 58 + lengthRestoreCost + indexClearCost +
          tailClearCost - 2 =
          G + finishGas + 56 + lengthRestoreCost + indexClearCost +
            tailClearCost := by omega
      rw [hg]
      exact htailLength
  have hstoreMoved : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨indexKey :: next :: stack, M,
          G + finishGas + 58 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (Ninst.sstore ::: pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord arrayLengthWord +++
        pushB256 1 ::: swap 0 ::: sub ::: pushB256 arrayLengthSlot :::
        Ninst.sstore ::: pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hindexHole hindexOrig hmovedIndexCost
        hwarmIndexHole (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      htailPrefix
  have hmovedTag : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨target :: next :: stack, M,
          G + finishGas + 64 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [indexKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 64 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost - 6 =
          G + finishGas + 58 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost := by omega
      rw [hg]
      exact hstoreMoved
  have hmovedLast : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨next :: stack, M,
          G + finishGas + 70 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (2) [3]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered lastTargetWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlastValue, hlastMemory]
      have hg : G + finishGas + 70 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost - 6 =
          G + finishGas + 64 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost := by omega
      rw [hg]
      exact hmovedTag
  have hmovedPrefix : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨stack, M,
          G + finishGas + 76 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (loadWord removedIndexWord +++ loadWord lastTargetWord +++
        tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [3]
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered removedIndexWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hremovedValue, hremovedMemory]
      have hg : G + finishGas + 76 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost - 6 =
          G + finishGas + 70 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost := by omega
      rw [hg]
      exact hmovedLast
  have hstoreHole : Func.RunCompiled fs sevm
      (base.setMach
        ⟨arrayKey :: target :: stack, M,
          G + finishGas + 76 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (Ninst.sstore ::: loadWord removedIndexWord +++
        loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled harray harrayOrig hholeCost hwarmArray
        (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      hmovedPrefix
  have hholeTag : Func.RunCompiled fs sevm
      (base.setMach
        ⟨next :: target :: stack, M,
          G + finishGas + 82 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (2) [arrayKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 82 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost + holeCost - 6 =
          G + finishGas + 76 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost := by omega
      rw [hg]
      exact hstoreHole
  have hholeRemoved : Func.RunCompiled fs sevm
      (base.setMach
        ⟨target :: stack, M,
          G + finishGas + 88 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ loadWord lastTargetWord +++
        tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [3]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered removedIndexWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hremovedValue, hremovedMemory]
      have hg : G + finishGas + 88 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost + holeCost - 6 =
          G + finishGas + 82 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost := by omega
      rw [hg]
      exact hholeTag
  have hholePrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, M,
          G + finishGas + 94 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ loadWord lastTargetWord +++
        tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [3]
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered lastTargetWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlastValue, hlastMemory]
      have hg : G + finishGas + 94 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost + holeCost - 6 =
          G + finishGas + 88 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost := by omega
      rw [hg]
      exact hholeRemoved
  have hg : G + finishGas + 94 + lengthRestoreCost + indexClearCost + tailClearCost +
      movedIndexCost + holeCost =
      G + finishGas + 94 + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost := by omega
  rw [hg] at hholePrefix
  simpa only [lastTargetIndexKey, prepend_append, fs,
    arrayKey, indexKey, holePost, movedPost, tailPost] using hholePrefix

/-! ## The cold-entry degenerate `removeTarget` walk

`removeTarget_toFinish_runCompiled` charges its three array-region `SLOAD`s
warm and demands the keys warm at entry.  This variant is the same walk in the
temporal convention: the three charges are hypothesis-supplied
`temporalSloadCost` equations, the walk threads the `temporalSloadBase`
successors, and the store suffix runs at the threaded state, where all three
keys are warm.  Fixed charge `139 = 439 - 300`. -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem removeTarget_toFinish_coldEntry_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next : B256) (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (idxSloadCost lenSloadCost arrSloadCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost finishGas G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (entrySize indexExtCost lengthExtCost lastExtCost : Nat)
    (hsize : M.size = entrySize) (halign : M.size % 32 = 0)
    (hentryLow : 640 ≤ entrySize)
    (hindexExtCost : calculateMemoryGasCost
        (memExtSize entrySize (removedIndexWord * 32).toNat 32) -
      calculateMemoryGasCost entrySize = indexExtCost)
    (hlengthExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 672) (arrayLengthWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 672) = lengthExtCost)
    (hlastExtCost : calculateMemoryGasCost
        (memExtSize (max entrySize 704) (lastTargetWord * 32).toNat 32) -
      calculateMemoryGasCost (max entrySize 704) = lastExtCost)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlength : base.getStorVal sevm.currentTarget
      arrayLengthSlot = next)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot next) = arrayOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hidxSloadCost : temporalSloadCost sevm base (indexSlot target) =
      idxSloadCost)
    (hlenSloadCost : temporalSloadCost sevm
      (temporalSloadBase sevm base (indexSlot target)) arrayLengthSlot =
      lenSloadCost)
    (harrSloadCost : temporalSloadCost sevm
      (temporalSloadBase sevm
        (temporalSloadBase sevm base (indexSlot target)) arrayLengthSlot)
      (arrayEntrySlot next) = arrSloadCost)
    (hholeCost : sstoreValueCost arrayOriginal target target = holeCost)
    (hmovedIndexCost : sstoreValueCost indexOriginal next next =
      movedIndexCost)
    (htailClearCost : sstoreValueCost arrayOriginal target 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal next 0 =
      indexClearCost)
    (hsub : next - 1 = oldLength)
    (hgasFinal : gCallStipend < G + finishGas + 12 + indexClearCost)
    (hstatic : sevm.isStatic = false)
    (post : Devm)
    (hfinish :
      let coldBase := temporalSloadBase sevm
        (temporalSloadBase sevm
          (temporalSloadBase sevm base (indexSlot target)) arrayLengthSlot)
        (arrayEntrySlot next)
      let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
      let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
      let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
      let tailPost := entryClearPost sevm coldBase target next
      let removePost := indexClearPost sevm tailPost target oldLength
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, MLast, G + finishGas⟩)
        finishSetPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 139 + lastExtCost + indexExtCost + lengthExtCost +
          idxSloadCost + lenSloadCost + arrSloadCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget post := by
  dsimp only at hfinish
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let base1 := temporalSloadBase sevm base (indexSlot target)
  let base2 := temporalSloadBase sevm base1 arrayLengthSlot
  let base3 := temporalSloadBase sevm base2 (arrayEntrySlot next)
  let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    target.toBytes
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
  have hsizeLength : MLength.size = max entrySize 704 := by
    dsimp only [MLength]
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide,
      hsizeIndex, show ceil32 704 = 704 by decide]
    split <;> omega
  have hsizeLast : MLast.size = max entrySize 736 := by
    dsimp only [MLast]
    rw [Mem.size_write_word_at,
      show (lastTargetWord * 32).toNat + 32 = 736 by decide,
      hsizeLength]
    split
    · omega
    · rw [show ceil32 736 = 736 by decide]
      omega
  have halignIndex : MIndex.size % 32 = 0 :=
    Mem.aligned_write_word halign
  have halignLength : MLength.size % 32 = 0 :=
    Mem.aligned_write_word halignIndex
  have halignLast : MLast.size % 32 = 0 :=
    Mem.aligned_write_word halignLength
  have sliceBeforeIndex {word : B256}
      (hbefore : (word * 32).toNat + 32 ≤
        (removedIndexWord * 32).toNat) :
      Bytes.toB256 (imgIndex.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hbefore]
  have sliceBeforeLength {word : B256}
      (hbefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat) :
      Bytes.toB256 (imgLength.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (imgIndex.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hbefore]
  have sliceBeforeLast {word : B256}
      (hbefore : (word * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat) :
      Bytes.toB256 (imgLast.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (imgLength.sliceD (word * 32).toNat 32 0) := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hbefore]
  have earlierLast {word : B256}
      (hindexBefore : (word * 32).toNat + 32 ≤
        (removedIndexWord * 32).toNat)
      (hlengthBefore : (word * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat)
      (hlastBefore : (word * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat) :
      Bytes.toB256 (imgLast.sliceD (word * 32).toNat 32 0) =
        Bytes.toB256 (img.sliceD (word * 32).toNat 32 0) :=
    (sliceBeforeLast hlastBefore).trans
      ((sliceBeforeLength hlengthBefore).trans
        (sliceBeforeIndex hindexBefore))
  have htargetLast : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target :=
    (earlierLast (by decide) (by decide) (by decide)).trans htarget
  have hremovedLength : Bytes.toB256
      (imgLength.sliceD (removedIndexWord * 32).toNat 32 0) = next := by
    rw [sliceBeforeLength (word := removedIndexWord) (by decide)]
    dsimp only [imgIndex]
    rw [show 32 = next.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hremovedLast : Bytes.toB256
      (imgLast.sliceD (removedIndexWord * 32).toNat 32 0) = next :=
    (sliceBeforeLast (word := removedIndexWord) (by decide)).trans
      hremovedLength
  have hlengthLast : Bytes.toB256
      (imgLast.sliceD (arrayLengthWord * 32).toNat 32 0) = next := by
    rw [sliceBeforeLast (word := arrayLengthWord) (by decide)]
    dsimp only [imgLength]
    rw [show 32 = next.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hlastLast : Bytes.toB256
      (imgLast.sliceD (lastTargetWord * 32).toNat 32 0) = target := by
    dsimp only [imgLast]
    rw [show 32 = target.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hindex1 : base1.getStorVal sevm.currentTarget arrayLengthSlot =
      next := by
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget arrayLengthSlot = next
    rw [temporalSloadBase_getStorVal]
    exact hlength
  have harray2 : base2.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target := by
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget (arrayEntrySlot next) =
      target
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget (arrayEntrySlot next) =
      target
    rw [temporalSloadBase_getStorVal]
    exact harray
  have harray3 : base3.getStorVal sevm.currentTarget arrayKey = target := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot next)).getStorVal sevm.currentTarget
      (arrayEntrySlot next) = target
    rw [temporalSloadBase_getStorVal]
    exact harray2
  have hindex3 : base3.getStorVal sevm.currentTarget indexKey = next := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot next)).getStorVal sevm.currentTarget
      (indexSlot target) = next
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget (indexSlot target) = next
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget (indexSlot target) =
      next
    rw [temporalSloadBase_getStorVal]
    exact hindex
  have hlength3 : base3.getStorVal sevm.currentTarget arrayLengthSlot =
      next := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot next)).getStorVal sevm.currentTarget arrayLengthSlot =
      next
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget arrayLengthSlot = next
    rw [temporalSloadBase_getStorVal]
    exact hindex1
  have hwarmIndex3 : (sevm.currentTarget, indexKey) ∈
      base3.accessedStorageKeys :=
    temporalSloadBase_preserves_warm sevm base2 (arrayEntrySlot next) _
      (temporalSloadBase_preserves_warm sevm base1 arrayLengthSlot _
        (temporalSloadBase_warm sevm base (indexSlot target)))
  have hwarmLength3 : (sevm.currentTarget, arrayLengthSlot) ∈
      base3.accessedStorageKeys :=
    temporalSloadBase_preserves_warm sevm base2 (arrayEntrySlot next) _
      (temporalSloadBase_warm sevm base1 arrayLengthSlot)
  have hwarmArray3 : (sevm.currentTarget, arrayKey) ∈
      base3.accessedStorageKeys :=
    temporalSloadBase_warm sevm base2 (arrayEntrySlot next)
  let tailPost := entryClearPost sevm base3 target next
  let removePost := indexClearPost sevm tailPost target oldLength
  have hstores := removeTarget_storePrefix_runCompiled
    dp sevm base3 MLast imgLast target oldLength next stack hstack
    arrayOriginal
    indexOriginal lengthOriginal holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost finishGas G hreadsLast htargetLast
    hremovedLast hlengthLast hlastLast
    htargetValid hnextNonzero hnextBound
    (by rw [hsizeLast]; exact Nat.le_max_right _ _) halignLast
    harray3 hindex3
    hlength3 harrayOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost
    htailClearCost hlengthRestoreCost hindexClearCost hwarmArray3 hwarmIndex3
    hwarmLength3 hsub hgasFinal hstatic post
    (by simpa only [MIndex, MLength, MLast, base3, base2, base1,
      tailPost, removePost] using hfinish)
  let fs := (runtime dp).main :: (runtime dp).aux
  have hsaveLast : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨lastTargetWord * 32 :: target :: stack, MLength,
          G + finishGas + 97 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
      (Ninst.mstore ::: loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_mstore_of
        (G := G + finishGas + 94 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) (M := MLast) rfl
        (Devm.extCost_of_size
          (i := (lastTargetWord * 32).toNat) (sz := 32) (e := lastExtCost)
          hsizeLength hlastExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · simpa only [fs, MLast, Devm.setMach_setMach,
        Devm.memory_setMach] using hstores
  have hlastLoad : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨target :: stack, MLength,
          G + finishGas + 100 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
      (mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (1)
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 100 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost - 3 =
          G + finishGas + 97 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hsaveLast
  have harrSloadStep : Ninst.RunCompiled sevm
      (base2.setMach
        ⟨arrayKey :: stack, MLength,
          G + finishGas + 100 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost⟩)
      Ninst.sload
      (base3.setMach
        ⟨target :: stack, MLength,
          G + finishGas + 100 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := base2)
      (key := arrayEntrySlot next) (value := target) (stack := stack)
      (M := MLength)
      (G := G + finishGas + 100 + lastExtCost + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost)
      harray2 (by omega)
    rw [show temporalSloadCost sevm base2 (arrayEntrySlot next) =
      arrSloadCost from harrSloadCost] at h
    exact h
  have hloadLastStorage : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨arrayKey :: stack, MLength,
          G + finishGas + 100 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost⟩)
      (Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post :=
    Func.RunCompiled.next harrSloadStep hlastLoad
  have hlastTag : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨next :: stack, MLength,
          G + finishGas + 106 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost⟩)
      (tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [arrayKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 106 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost +
          arrSloadCost - 6 =
          G + finishGas + 100 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost := by omega
      rw [hg]
      exact hloadLastStorage
  have hlengthValue :
      (MLength.read (arrayLengthWord * 32).toNat 32).1.toB256 = next := by
    rw [Mem.Reads.read hreadsLength]
    dsimp only [imgLength]
    rw [show 32 = next.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hlengthMemory :
      (MLength.read (arrayLengthWord * 32).toNat 32).2 = MLength := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halignLength (by
      rw [hsizeLength, show (arrayLengthWord * 32).toNat + 32 = 704 by decide]
      exact Nat.le_max_right _ _))]
  have hlastPrefix : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨stack, MLength,
          G + finishGas + 112 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost⟩)
      (loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sload :::
        mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (2) [3]
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halignLength (by
        rw [hsizeLength, show (arrayLengthWord * 32).toNat + 32 = 704 by decide]
        exact Nat.le_max_right _ _)]
      norm_num [gVerylow]
    case a =>
      rw [hlengthValue, hlengthMemory]
      have hg : G + finishGas + 112 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost +
          arrSloadCost - 6 =
          G + finishGas + 106 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost := by omega
      rw [hg]
      exact hlastTag
  have hsaveLength : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨arrayLengthWord * 32 :: next :: stack, MIndex,
          G + finishGas + 115 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost⟩)
      (Ninst.mstore ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_mstore_of
        (G := G + finishGas + 112 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost + arrSloadCost)
        (M := MLength) rfl
        (Devm.extCost_of_size
          (i := (arrayLengthWord * 32).toNat) (sz := 32) (e := lengthExtCost)
          hsizeIndex hlengthExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlastPrefix
  have hsaveLengthPrefix : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨next :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost⟩)
      (mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (1)
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 118 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost + arrSloadCost - 3 =
          G + finishGas + 115 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost := by omega
      rw [hg]
      exact hsaveLength
  have hlenSloadStep : Ninst.RunCompiled sevm
      (base1.setMach
        ⟨arrayLengthSlot :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost⟩)
      Ninst.sload
      (base2.setMach
        ⟨next :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := base1)
      (key := arrayLengthSlot) (value := next) (stack := stack)
      (M := MIndex)
      (G := G + finishGas + 118 + lastExtCost + lengthExtCost + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost + arrSloadCost)
      hindex1 (by omega)
    rw [show temporalSloadCost sevm base1 arrayLengthSlot =
      lenSloadCost from hlenSloadCost] at h
    exact h
  have hlengthLoad : Func.RunCompiled fs sevm
      (base1.setMach
        ⟨arrayLengthSlot :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost⟩)
      (Ninst.sload ::: mstoreAt arrayLengthWord +++
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sload :::
        mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post :=
    Func.RunCompiled.next hlenSloadStep hsaveLengthPrefix
  have hlengthPrefix : Func.RunCompiled fs sevm
      (base1.setMach
        ⟨stack, MIndex,
          G + finishGas + 121 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost⟩)
      (pushB256 arrayLengthSlot ::: Ninst.sload :::
        mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (1)
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case a =>
      have hg : G + finishGas + 121 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost + arrSloadCost + lenSloadCost - 3 =
          G + finishGas + 118 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost := by omega
      rw [hg]
      exact hlengthLoad
  have hsaveIndex : Func.RunCompiled fs sevm
      (base1.setMach
        ⟨removedIndexWord * 32 :: next :: stack, M,
          G + finishGas + 124 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost⟩)
      (Ninst.mstore ::: pushB256 arrayLengthSlot ::: Ninst.sload :::
        mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_mstore_of
        (G := G + finishGas + 121 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost + arrSloadCost + lenSloadCost)
        (M := MIndex) rfl
        (Devm.extCost_of_size
          (i := (removedIndexWord * 32).toNat) (sz := 32) (e := indexExtCost)
          hsize hindexExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlengthPrefix
  have hsaveIndexPrefix : Func.RunCompiled fs sevm
      (base1.setMach
        ⟨next :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost⟩)
      (mstoreAt removedIndexWord +++ pushB256 arrayLengthSlot :::
        Ninst.sload ::: mstoreAt arrayLengthWord +++
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sload :::
        mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (1)
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 127 + lastExtCost + indexExtCost +
          lengthExtCost + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost + arrSloadCost +
          lenSloadCost - 3 =
          G + finishGas + 124 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost := by omega
      rw [hg]
      exact hsaveIndex
  have hidxSloadStep : Ninst.RunCompiled sevm
      (base.setMach
        ⟨indexKey :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost + idxSloadCost⟩)
      Ninst.sload
      (base1.setMach
        ⟨next :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := base)
      (key := indexSlot target) (value := next) (stack := stack)
      (M := M)
      (G := G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
        holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost + arrSloadCost + lenSloadCost)
      hindex (by omega)
    rw [show temporalSloadCost sevm base (indexSlot target) =
      idxSloadCost from hidxSloadCost] at h
    exact h
  have hindexLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨indexKey :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost + idxSloadCost⟩)
      (Ninst.sload ::: mstoreAt removedIndexWord +++
        pushB256 arrayLengthSlot ::: Ninst.sload :::
        mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post :=
    Func.RunCompiled.next hidxSloadStep hsaveIndexPrefix
  have htargetValue :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    rw [hsize, show (targetWord * 32).toNat + 32 = 544 by decide]
    omega
  have htargetMemory :
      (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have hindexTag : Func.RunCompiled fs sevm
      (base.setMach
        ⟨target :: stack, M,
          G + finishGas + 133 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost + idxSloadCost⟩)
      (tagTop indexRegion +++ Ninst.sload ::: mstoreAt removedIndexWord +++
        pushB256 arrayLengthSlot ::: Ninst.sload :::
        mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [indexKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 133 + lastExtCost + indexExtCost +
          lengthExtCost + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost + arrSloadCost + lenSloadCost +
          idxSloadCost - 6 =
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost + idxSloadCost := by
        omega
      rw [hg]
      exact hindexLoad
  have hindexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, M,
          G + finishGas + 139 + lastExtCost + indexExtCost + lengthExtCost +
            idxSloadCost + lenSloadCost + arrSloadCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
      (targetIndexKey +++ Ninst.sload ::: mstoreAt removedIndexWord +++
        pushB256 arrayLengthSlot ::: Ninst.sload :::
        mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [3]
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign htargetCovered]
      norm_num [gVerylow]
    case a =>
      rw [htargetValue, htargetMemory]
      have hg : G + finishGas + 139 + lastExtCost + indexExtCost +
          lengthExtCost + idxSloadCost + lenSloadCost + arrSloadCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 6 =
          G + finishGas + 133 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost + lenSloadCost + idxSloadCost := by
        omega
      rw [hg]
      exact hindexTag
  simp only [removeTarget]
  simpa only [fs, MLast] using hindexPrefix

/-! ## The `pauseAfterSet` walk with an existential boundary

`pauseAfterSet_toSuccess_runCompiled` fixes its final state before quantifying
over the `pauseSuccess` boundary state, and the boundary facts pin that state
only up to membership-extensionality of its accessed sets — so no fixed final
state serves every conforming boundary state, and the continuation premise is
unsatisfiable.  This variant exports the actual boundary state existentially
instead: the consumer receives `mid`, its projection facts, and a closure
extending any continuation walk from `mid` to the full `pauseAfterSet` walk.

The two responder-crossing wrappers are file-scoped in
`Blanc/LidoCircuitBreakerPauseSuffixWalk.lean` and transcribed verbatim; they
belong upstream. -/


private lemma responder_call_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = calleeCode)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : 118 ≤ G) (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = G - 117 ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ devm.accessedAddresses) ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal target.toAdr 0 := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    decide
  have hdel : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr) target.toAdr =
      ⟨false, target.toAdr,
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
          target.toAdr, 0,
        addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
          target.toAdr⟩ := by
    unfold accessDelegation
    simp only [show (addAccessedAddress
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr).state.getCode target.toAdr =
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr from rfl, hnodel]
  set d0 := addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
    target.toAdr with hd0
  have hd0gas : d0.gasLeft = G := by
    rw [show d0.gasLeft = devm.gasLeft from rfl, hgas]
  have hacc : accessCost target.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses + 0 =
      gasWarmAccess := by
    show accessCost target.toAdr devm.accessedAddresses + 0 = gasWarmAccess
    unfold accessCost
    rw [if_pos hwarm]
    omega
  obtain ⟨mcc, mcs, hsplit⟩ : ∃ mcc mcs,
      calculateMsgCallGas 0 (Nat.toB256 G).toNat d0.gasLeft 0 gasWarmAccess =
        ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs17, hcross, hgasout⟩ :
      17 ≤ mcs ∧ mcc + 0 ≤ G ∧ G - (mcc + 0) + (mcs - 17) = G - 117 := by
    have hGnat : (Nat.toB256 G).toNat = G := B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin : min G (except64th (G - 0 - 100)) = except64th (G - 100) := by
      have h1 : except64th (G - 0 - 100) ≤ G := by
        unfold except64th; omega
      rw [Nat.min_eq_right h1]
      norm_num
    rw [hmin] at hsplit
    have h1 : except64th (G - 100) + 100 = mcc := congrArg Prod.fst hsplit
    have h2 : except64th (G - 100) + 0 = mcs := congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, haa, stmid, hsub, hstate⟩ :=
    runCompiled_call_zero_value_responder (gw := Nat.toB256 G) (cw := target)
      hstk (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = calleeCode from hcode) hmcs17 hroom
  refine ⟨post, hrun, hstack, hmem, ?_, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, ?_, stmid, hsub, hstate⟩
  · rw [hgasl, hd0gas]
    exact hgasout
  · intro a
    rw [haa a]
    show a ∈ devm.accessedAddresses.insert target.toAdr ↔
      a ∈ devm.accessedAddresses
    constructor
    · intro hx
      rcases Std.HashSet.mem_insert.mp hx with he | hx'
      · exact (eq_of_beq he) ▸ hwarm
      · exact hx'
    · intro hx
      exact Std.HashSet.mem_insert.mpr (Or.inr hx)

private lemma responder_statcall_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = calleeCode)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : 118 ≤ G) (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = G - 117 ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ devm.accessedAddresses) ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal target.toAdr 0 := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    decide
  have hdel : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr) target.toAdr =
      ⟨false, target.toAdr,
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
          target.toAdr, 0,
        addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
          target.toAdr⟩ := by
    unfold accessDelegation
    simp only [show (addAccessedAddress
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr).state.getCode target.toAdr =
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr from rfl, hnodel]
  set d0 := addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
    target.toAdr with hd0
  have hd0gas : d0.gasLeft = G := by
    rw [show d0.gasLeft = devm.gasLeft from rfl, hgas]
  have hacc : accessCost target.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses + 0 =
      gasWarmAccess := by
    show accessCost target.toAdr devm.accessedAddresses + 0 = gasWarmAccess
    unfold accessCost
    rw [if_pos hwarm]
    omega
  obtain ⟨mcc, mcs, hsplit⟩ : ∃ mcc mcs,
      calculateMsgCallGas 0 (Nat.toB256 G).toNat d0.gasLeft 0 gasWarmAccess =
        ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs17, hcross, hgasout⟩ :
      17 ≤ mcs ∧ mcc + 0 ≤ G ∧ G - (mcc + 0) + (mcs - 17) = G - 117 := by
    have hGnat : (Nat.toB256 G).toNat = G := B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin : min G (except64th (G - 0 - 100)) = except64th (G - 100) := by
      have h1 : except64th (G - 0 - 100) ≤ G := by
        unfold except64th; omega
      rw [Nat.min_eq_right h1]
      norm_num
    rw [hmin] at hsplit
    have h1 : except64th (G - 100) + 100 = mcc := congrArg Prod.fst hsplit
    have h2 : except64th (G - 100) + 0 = mcs := congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, haa, stmid, hsub, hstate⟩ :=
    runCompiled_statcall_responder (gw := Nat.toB256 G) (tw := target)
      hstk (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = calleeCode from hcode) hmcs17 hroom
  refine ⟨post, hrun, hstack, hmem, ?_, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, ?_, stmid, hsub, hstate⟩
  · rw [hgasl, hd0gas]
    exact hgasout
  · intro a
    rw [haa a]
    show a ∈ devm.accessedAddresses.insert target.toAdr ↔
      a ∈ devm.accessedAddresses
    constructor
    · intro hx
      rcases Std.HashSet.mem_insert.mp hx with he | hx'
      · exact (eq_of_beq he) ▸ hwarm
      · exact hx'
    · intro hx
      exact Std.HashSet.mem_insert.mpr (Or.inr hx)


set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
/-- `pauseAfterSet` from its entry to the `pauseSuccess` boundary, with the
boundary state exported existentially.  Same route, charges and hypotheses as
`pauseAfterSet_toSuccess_runCompiled`; the difference is the conclusion's
shape, which a composition can actually consume. -/
theorem pauseAfterSet_toSuccess_exists_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (target duration : B256) (M : Mem) (img : Bytes)
    (codeCost Gb : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hduration : Bytes.toB256
      (img.sliceD (durationWord * 32).toNat 32 0) = duration)
    (hsize : M.size = 768)
    (hcodeCost : temporalAccountAccessCost base target.toAdr = codeCost)
    (hcalleeCode : base.getCode target.toAdr = calleeCode)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hbound : Gb + 359 < 2 ^ 256) :
    ∃ mid : Devm,
      mid.stack = [] ∧
      mid.memory = pauseDecodedMemory M duration ∧
      mid.gasLeft = Gb ∧
      mid.error = base.error ∧
      mid.output = base.output ∧
      mid.returnData = (1 : B256).toBytes ∧
      mid.logs = base.logs ∧
      mid.refundCounter = base.refundCounter ∧
      mid.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty ∧
      mid.transientStorage = base.transientStorage ∧
      (∀ k, k ∈ mid.accessedStorageKeys ↔ k ∈ base.accessedStorageKeys) ∧
      (∀ a, a ∈ mid.accessedAddresses ↔
        (a = target.toAdr ∨ a ∈ base.accessedAddresses)) ∧
      (∃ st₁ st₂ : State,
        base.state.subBal sevm.currentTarget 0 = some st₁ ∧
        (st₁.addBal target.toAdr 0).subBal sevm.currentTarget 0 = some st₂ ∧
        mid.state = st₂.addBal target.toAdr 0) ∧
      ∀ post : Devm,
        Func.RunCompiled fs sevm mid pauseSuccess post →
        Func.RunCompiled fs sevm
          (base.setMach ⟨[], M, Gb + 427 + codeCost⟩) pauseAfterSet post := by
  have halign : M.size % 32 = 0 := by omega
  -- the staged images and their windows
  have hwf1 : Mem.Wf (M.write 256 pauseForSelector.toBytes) := hwf.write _ _
  have hwf2 : Mem.Wf ((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes) := hwf1.write _ _
  have hsize1 : (M.write 256 pauseForSelector.toBytes).size = 768 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize
  have hsize2 : ((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).size = 768 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize1
  have hsize3 : (((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).write 256 isPausedSelector.toBytes).size = 768 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize2
  have halign2 : ((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).size % 32 = 0 := by omega
  have halign3 : (((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).write 256 isPausedSelector.toBytes).size % 32 = 0 := by
    omega
  -- entry-image reads
  have htargetMemory0 : (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have htargetValue0 :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  -- duration read from the selector-staged image
  have hreads1 : Mem.Reads (M.write 256 pauseForSelector.toBytes)
      (Bytes.writeAt img 256 pauseForSelector.toBytes) :=
    Mem.Reads.write hwf hreads 256 _
  have hdurationMemory1 :
      ((M.write 256 pauseForSelector.toBytes).read
        (durationWord * 32).toNat 32).2 =
      M.write 256 pauseForSelector.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le (by omega) (by
      have hoff : (durationWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have hdurationValue1 :
      ((M.write 256 pauseForSelector.toBytes).read
        (durationWord * 32).toNat 32).1.toB256 = duration := by
    rw [Mem.Reads.read hreads1]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact hduration
  -- target read from the two-word-staged image
  have hreads2 : Mem.Reads
      ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
      (Bytes.writeAt (Bytes.writeAt img 256 pauseForSelector.toBytes) 288
        duration.toBytes) :=
    Mem.Reads.write hwf1 hreads1 288 _
  have htargetMemory2 :
      (((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).read (targetWord * 32).toNat 32).2 =
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign2 (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have htargetValue2 :
      (((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).read (targetWord * 32).toNat 32).1.toB256 =
      target := by
    rw [Mem.Reads.read hreads2]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact htarget
  -- target read from the fully staged image
  have hreads3 : Mem.Reads (((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).write 256 isPausedSelector.toBytes)
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 256
        pauseForSelector.toBytes) 288 duration.toBytes) 256
        isPausedSelector.toBytes) :=
    Mem.Reads.write hwf2 hreads2 256 _
  have htargetMemory3 :
      ((((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).write 256 isPausedSelector.toBytes).read
          (targetWord * 32).toNat 32).2 =
      ((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).write 256 isPausedSelector.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign3 (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have htargetValue3 :
      ((((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).write 256 isPausedSelector.toBytes).read
          (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads3]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact htarget
  -- the decoded word read back
  have honeBytes : (1 : B256).toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes (1 : B256)
    rw [h] at hlen
    simp at hlen
  have hdecodedValue :
      ((pauseDecodedMemory M duration).read 0 32).1.toB256 = 1 := by
    rw [pauseDecodedMemory, show (32 : Nat) =
      (1 : B256).toBytes.length from (B256.length_toBytes 1).symm,
      Mem.read_write_zero _ honeBytes, B256.toB256_toBytes]
  have hsize4 : (pauseDecodedMemory M duration).size = 768 := by
    rw [pauseDecodedMemory, pauseStagedMemory,
      Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize3
  have hdecodedMemory :
      ((pauseDecodedMemory M duration).read 0 32).2 =
        pauseDecodedMemory M duration := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le (by omega) (by omega))]
  -- the first crossing
  obtain ⟨post1, hrun1, hstk1, hmem1, hgas1, herr1, hout1, hret1, hlogs1,
    hrefund1, hatd1, htrans1, hask1, haa1, st₁, hsub1, hstate1⟩ :=
    responder_call_crossing (sevm := sevm)
      (devm := (temporalAccountAccessBase base target.toAdr).setMach
        ⟨[Nat.toB256 (Gb + 359), target, 0, 284, 36, 0, 0],
          (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
          Gb + 359⟩)
      (target := target) (iiw := 284) (isw := 36) (oiw := 0) (osw := 0)
      (s := []) (G := Gb + 359)
      rfl rfl
      (by
        show ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[Nat.toB256 (Gb + 359), target, 0, 284, 36, 0, 0],
            (M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes, Gb + 359⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize2]; decide))
      (by
        show (temporalAccountAccessBase base target.toAdr).getCode
          target.toAdr = calleeCode
        rw [temporalAccountAccessBase_getCode]
        exact hcalleeCode)
      (temporalAccountAccessBase_warm base target.toAdr)
      hdepth hnp (by omega) hbound (by simp)
  have hgas1' : post1.gasLeft = Gb + 242 := by
    rw [hgas1]
    omega
  have hmem1' : post1.memory =
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes := by
    simp only [Devm.memory_setMach] at hmem1
    rw [hmem1,
      show (1 : B256).toBytes.take ((0 : B256)).toNat = [] by decide,
      show ((0 : B256)).toNat = 0 by decide,
      Mem.extends_covered (by rw [hsize2]; decide)]
    rfl
  have heta1 : post1 = post1.setMach ⟨[1],
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
      Gb + 242⟩ := by
    rw [← hstk1, ← hmem1', ← hgas1']
    rfl
  -- the second crossing
  have hcode1 : post1.state.getCode target.toAdr = calleeCode := by
    rw [hstate1, State.addBal_getCode, State.subBal_getCode hsub1]
    show (temporalAccountAccessBase base target.toAdr).state.getCode
      target.toAdr = calleeCode
    rw [temporalAccountAccessBase_state]
    exact hcalleeCode
  obtain ⟨post2, hrun2, hstk2, hmem2, hgas2, herr2, hout2, hret2, hlogs2,
    hrefund2, hatd2, htrans2, hask2, haa2, st₂, hsub2, hstate2⟩ :=
    responder_statcall_crossing (sevm := sevm)
      (devm := post1.setMach
        ⟨[Nat.toB256 (Gb + 198), target, 284, 4, 0, 32],
          ((M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes).write 256 isPausedSelector.toBytes,
          Gb + 198⟩)
      (target := target) (iiw := 284) (isw := 4) (oiw := 0) (osw := 32)
      (s := []) (G := Gb + 198)
      rfl rfl
      (by
        show (post1.setMach
          ⟨[Nat.toB256 (Gb + 198), target, 284, 4, 0, 32],
            ((M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes).write 256 isPausedSelector.toBytes,
            Gb + 198⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize3]; decide))
      (by
        show post1.state.getCode target.toAdr = calleeCode
        exact hcode1)
      ((haa1 target.toAdr).mpr (temporalAccountAccessBase_warm base
        target.toAdr))
      hdepth hnp (by omega) (by omega) (by simp)
  have hgas2' : post2.gasLeft = Gb + 81 := by
    rw [hgas2]
    omega
  have hmem2' : post2.memory = pauseDecodedMemory M duration := by
    simp only [Devm.memory_setMach] at hmem2
    rw [hmem2,
      show (1 : B256).toBytes.take ((32 : B256)).toNat =
        (1 : B256).toBytes by decide,
      show ((0 : B256)).toNat = 0 by decide,
      Mem.extends_covered (by rw [hsize3]; decide)]
    rfl
  have heta2 : post2 = post2.setMach ⟨[1], pauseDecodedMemory M duration,
      Gb + 81⟩ := by
    rw [← hstk2, ← hmem2', ← hgas2']
    rfl
  -- the boundary state's facts, chained through both crossings
  have hltFlag : (Nat.toB256 post2.returnData.length <? (32 : B256)) = 0 := by
    rw [hret2, B256.length_toBytes]
    decide
  have herrB : post2.error = base.error := by
    rw [herr2]
    show post1.error = base.error
    rw [herr1]
    exact temporalAccountAccessBase_error base target.toAdr
  have houtB : post2.output = base.output := by
    rw [hout2]
    show post1.output = base.output
    rw [hout1]
    exact temporalAccountAccessBase_output base target.toAdr
  have hlogsB : post2.logs = base.logs := by
    rw [hlogs2]
    show post1.logs = base.logs
    rw [hlogs1]
    exact temporalAccountAccessBase_logs base target.toAdr
  have hrefundB : post2.refundCounter = base.refundCounter := by
    rw [hrefund2]
    show post1.refundCounter = base.refundCounter
    rw [hrefund1]
    exact temporalAccountAccessBase_refundCounter base target.toAdr
  have hatdB : post2.accountsToDelete.isEmpty =
      base.accountsToDelete.isEmpty := by
    rw [hatd2]
    show post1.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty
    rw [hatd1]
    exact congrArg Std.HashSet.isEmpty
      (temporalAccountAccessBase_accountsToDelete base target.toAdr)
  have htransB : post2.transientStorage = base.transientStorage := by
    rw [htrans2]
    show post1.transientStorage = base.transientStorage
    rw [htrans1]
    exact temporalAccountAccessBase_transientStorage base target.toAdr
  have haskB : ∀ k, k ∈ post2.accessedStorageKeys ↔
      k ∈ base.accessedStorageKeys := by
    intro k
    refine (hask2 k).trans ((hask1 k).trans ?_)
    show k ∈ (temporalAccountAccessBase base target.toAdr
      ).accessedStorageKeys ↔ k ∈ base.accessedStorageKeys
    rw [temporalAccountAccessBase_accessedStorageKeys]
  have haaB : ∀ a, a ∈ post2.accessedAddresses ↔
      (a = target.toAdr ∨ a ∈ base.accessedAddresses) := by
    intro a
    refine (haa2 a).trans ((haa1 a).trans ?_)
    show a ∈ (temporalAccountAccessBase base target.toAdr
      ).accessedAddresses ↔ (a = target.toAdr ∨ a ∈ base.accessedAddresses)
    exact temporalAccountAccessBase_mem base target.toAdr a
  have hsub1' : base.state.subBal sevm.currentTarget 0 = some st₁ := by
    rw [← temporalAccountAccessBase_state base target.toAdr]
    exact hsub1
  have hsub2' : (st₁.addBal target.toAdr 0).subBal sevm.currentTarget 0 =
      some st₂ := by
    rw [← hstate1]
    exact hsub2
  refine ⟨post2.setMach ⟨[], pauseDecodedMemory M duration, Gb⟩,
    rfl, rfl, rfl, herrB, houtB, hret2, hlogsB, hrefundB, hatdB, htransB,
    haskB, haaB, ⟨st₁, st₂, hsub1', hsub2', hstate2⟩, ?_⟩
  intro post hwalk
  -- segment C: the decode, from the second crossing to the boundary
  have hC : Func.RunCompiled fs sevm
      (post2.setMach ⟨[1], pauseDecodedMemory M duration, Gb + 81⟩)
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult)) post := by
    have hisz : ((pauseDecodedMemory M duration).read 0 32).1.toB256 =? 0 =
        (0 : B256) := by
      rw [hdecodedValue]
      decide
    have heq : (1 : B256) =?
        ((pauseDecodedMemory M duration).read 0 32).1.toB256 = 1 := by
      rw [hdecodedValue]
      decide
    func_run (14) [0, 0, 3, 0, 1]
    case h_cost =>
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_zero_of_le (by omega) (by omega)]
      norm_num [gVerylow]
    case h_arm =>
      have hg : Gb + 81 - 81 = Gb := by omega
      rw [hg, show ((0 : B256) * 32).toNat = 0 from by decide, hdecodedMemory]
      exact hwalk
  -- segment B: from the first crossing to the second
  have hB : Func.RunCompiled fs sevm
      (post1.setMach ⟨[1],
        (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
        Gb + 242⟩)
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?>
          (pushB256 isPausedSelector ::: mstoreAt 8 +++
            pushList [32, 0, 4, 0x11c] +++ loadWord targetWord +++
            Ninst.gas ::: Ninst.statcall ::: Ninst.iszero :::
            ((Func.call bubbleRevertSlot) <?> decodePausedResult)))) post := by
    func_run (12) [0, 0, 3]
    all_goals try simp_rw [show ((8 : B256) * 32).toNat = 256 by decide]
    all_goals try simp_rw [htargetMemory3]
    case h_ext =>
      exact Devm.extCost_zero_of_le halign2 (by omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign3 (by
        have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case a =>
      rw [htargetValue3]
      have hg : Gb + 242 - 44 = Gb + 198 := by omega
      rw [hg]
      refine Func.RunCompiled.next hrun2 ?_
      rw [heta2]
      exact hC
  -- segment A2: the guard's live arm and the CALL staging
  have hA2 : Func.RunCompiled fs sevm
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[calleeCode.size.toB256, target], M, Gb + 418⟩)
      (Ninst.iszero :::
        ((Func.call emptyRevertSlot) <?>
          (Ninst.pop :::
            pushB256 pauseForSelector ::: mstoreAt 8 +++
            loadWord durationWord +++ mstoreAt 9 +++
            pushList [0, 0, 36, 0x11c, 0] +++ loadWord targetWord +++
            Ninst.gas ::: Ninst.call ::: Ninst.iszero :::
            ((Func.call bubbleRevertSlot) <?>
              (pushB256 isPausedSelector ::: mstoreAt 8 +++
                pushList [32, 0, 4, 0x11c] +++ loadWord targetWord +++
                Ninst.gas ::: Ninst.statcall ::: Ninst.iszero :::
                ((Func.call bubbleRevertSlot) <?> decodePausedResult))))))
      post := by
    func_run (18) [0, 0, 3, 0, 3]
    all_goals try simp_rw [show ((8 : B256) * 32).toNat = 256 by decide]
    all_goals try simp_rw [show ((9 : B256) * 32).toNat = 288 by decide]
    all_goals try simp_rw [hdurationMemory1]
    all_goals try simp_rw [hdurationValue1]
    all_goals try simp_rw [htargetMemory2]
    case h_ext =>
      exact Devm.extCost_zero_of_le halign (by omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le (by omega) (by
        have hoff : (durationWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case h_ext =>
      exact Devm.extCost_zero_of_le (by omega) (by omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign2 (by
        have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case a =>
      rw [htargetValue2]
      have hg : Gb + 418 - 59 = Gb + 359 := by omega
      rw [hg]
      refine Func.RunCompiled.next hrun1 ?_
      rw [heta1]
      exact hB
  -- the entry: the target load and the code-size guard
  have hextStep : Ninst.RunCompiled sevm
      (base.setMach ⟨[target, target], M, Gb + 418 + codeCost⟩)
      Ninst.extcodesize
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[calleeCode.size.toB256, target], M, Gb + 418⟩) := by
    have h := temporal_extcodesize_runCompiled (sevm := sevm) (base := base)
      (x := target) (v := calleeCode.size.toB256) (stack := [target])
      (M := M) (G := Gb + 418)
      (by rw [hcalleeCode]) (by simp)
    rw [hcodeCost] at h
    exact h
  func_run (3) [3]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega)]
    norm_num [gVerylow]
  case a =>
    rw [htargetValue0, htargetMemory0]
    have hg : Gb + 427 + codeCost - 9 = Gb + 418 + codeCost := by omega
    rw [hg]
    exact Func.RunCompiled.next hextStep hA2

/-! ## Seam transports

The crossings pin the boundary state's world as a zero-value `subBal`/`addBal`
chain over the pre-call state.  On storage projections that chain is the
identity, in the style of `Blanc/Weth10HolderFlowResult.lean`'s private
`state_addBal_getStor_eq`. -/

private theorem state_setBal_stor (st : State) (adr : Adr) (val : B256)
    (a : Adr) : ((st.setBal adr val).get a).stor = (st.get a).stor := by
  by_cases h : adr = a
  · subst h
    unfold State.setBal
    rw [State.get_set_self]
    rfl
  · exact congrArg Acct.stor (State.get_set_ne st h _)

private theorem state_addBal_stor (st : State) (adr : Adr) (val : B256)
    (a : Adr) : ((st.addBal adr val).get a).stor = (st.get a).stor := by
  unfold State.addBal
  exact state_setBal_stor st adr _ a

private theorem state_subBal_stor {st st' : State} {adr : Adr} {val : B256}
    (h : st.subBal adr val = some st') (a : Adr) :
    (st'.get a).stor = (st.get a).stor := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with h2
    subst h2
    exact state_setBal_stor st adr _ a

/-- The two-hop seam: the boundary state the crossings leave behind reads the
same storage as the pre-call state, cell for cell. -/
theorem seam_getStorVal {mid b : Devm} {ct : Adr} {t : B256}
    (hchain : ∃ st₁ st₂ : State,
      b.state.subBal ct 0 = some st₁ ∧
      (st₁.addBal t.toAdr 0).subBal ct 0 = some st₂ ∧
      mid.state = st₂.addBal t.toAdr 0)
    (a : Adr) (key : B256) :
    mid.getStorVal a key = b.getStorVal a key := by
  obtain ⟨st₁, st₂, hsub1, hsub2, hstate⟩ := hchain
  show (mid.state.get a).stor.get key = (b.state.get a).stor.get key
  rw [hstate, state_addBal_stor, state_subBal_stor hsub2,
    state_addBal_stor, state_subBal_stor hsub1]

end Blanc.LidoCircuitBreaker
