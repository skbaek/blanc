import Blanc.LidoCircuitBreakerPauseSuffixWalk

/-!
Composition kit for the pause witness-world runs.

`Blanc/LidoCircuitBreakerPauseWorldRun.lean` composes the complete `.ok`
`pause(address)` walks at the two witness worlds of
`Blanc/LidoCircuitBreakerPauseWorld.lean`.  Two of the landed legs cannot be
consumed there directly, and this leaf carries the bridging material:

* **Cold-entry `removeTarget` walks.**  The register-side
  `removeTarget_toFinish_runCompiled` and `removeTarget_swapPop_toFinish_runCompiled`
  families charge their array-region `SLOAD`s warm and demand those keys warm
  at entry — true at the unregister world, whose message pre-warms them, but
  false on the pause path: the pause worlds enter with empty accessed sets, and
  nothing between message entry and `removeTarget` touches the array region.
  The `…_coldEntry_runCompiled` variants below restate the same walks in the
  temporal convention: the read charges are hypothesis-supplied
  `temporalSloadCost` equations and the walk threads the warmed
  `temporalSloadBase` successors, so the store suffix runs at a state where the
  read keys really are warm.  The swap-pop variant additionally stores its hole
  and moved-index cells through the cold `SSTORE` sibling, because those two
  cells are written but never read on the pause path and so stay cold.  The
  private store-suffix lemmas they consume are file-scoped in
  `Blanc/LidoCircuitBreakerRegistrySubstrate.lean` and are transcribed here
  verbatim; they belong upstream, and should be deduplicated there the next
  time that file is opened.

* **A cold `SSTORE` in the temporal convention.**
  `temporal_sstore_cold_runCompiled` is the cold sibling of the substrate's
  warm-only `temporal_sstore_runCompiled`: the key joins the accessed set, the
  charge is `gasColdSload` plus the hypothesis-supplied value case, and the
  successor world is the ordinary `temporalSstorePost` over the warmed base —
  so a store suffix can thread a genuinely cold write exactly like a cold
  `SLOAD`.

* **Seam transports.**  The crossings pin the boundary state's world as a
  zero-value `subBal`/`addBal` chain; `seam_getStorVal` collapses that chain
  on storage projections, in the style of `Weth10HolderFlowResult.lean`'s
  `state_addBal_getStor_eq`.

The existential `pauseAfterSet` boundary leg that this module originally
carried has been promoted upstream to `pauseAfterSet_toSuccess_runCompiled` in
`Blanc/LidoCircuitBreakerPauseSuffixWalk.lean`; both witness-world
compositions now consume it there.
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
    simpa only [hg] using hstoreLength

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
  simpa only [hg, lastTargetIndexKey, prepend_append, fs,
    arrayKey, indexKey, holePost, movedPost, tailPost] using hholePrefix


/-! ## The cold `SSTORE`, in the temporal convention

`temporal_sstore_runCompiled` demands its key warm and charges the value case
alone.  This is its cold sibling, over `Ninst.runCompiled_sstore_cold`: the
key joins the accessed set, the charge is `gasColdSload` plus the
hypothesis-supplied value case, and the successor world is the ordinary
`temporalSstorePost` over the warmed base — so a store suffix can thread it
exactly like a cold `SLOAD`. -/

theorem temporal_sstore_cold_runCompiled
    {sevm : Sevm} {base : Devm} {key value current original : B256}
    {stack : List B256} {M : Mem} {G cost : Nat}
    (hcurrent : base.getStorVal sevm.currentTarget key = current)
    (horiginal : getOrigStorVal sevm sevm.currentTarget key = original)
    (hcost : sstoreValueCost original current value = cost)
    (hcold : (sevm.currentTarget, key) ∉ base.accessedStorageKeys)
    (hgas : gCallStipend < G + gasColdSload + cost)
    (hstatic : sevm.isStatic = false) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨key :: value :: stack, M, G + gasColdSload + cost⟩)
      Ninst.sstore
      ((temporalSstorePost sevm
          (addAccessedStorageKey base sevm.currentTarget key) key
          value).setMach
        ⟨stack, M, G⟩) := by
  apply Ninst.runCompiled_sstore_cold
      (c := gasColdSload + cost) (G := G)
  · rfl
  · exact hcold
  · simp only [Devm.gasLeft_setMach]
    omega
  · exact hstatic
  · simp only [Devm.getStorVal_setMach, hcurrent, horiginal]
    rw [hcost]
  · show sstoreNewRefundCounter value
        (getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) base.refundCounter =
      sstoreNewRefundCounter value
        (getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) base.refundCounter
    rfl
  · simp only [Devm.gasLeft_setMach]
    omega

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

/-! ## The cold-entry swap-and-pop `removeTarget` walk

The substrate's `removeTarget_swapPop_toFinish_runCompiled` demands **five**
keys warm at entry: the three the walk reads, plus the hole `arrayEntrySlot
idx` and the moved target's `indexSlot`, which it only writes.  On the pause
path the worlds enter cold and the walk itself warms only what it reads — so
the hole and moved-index `SSTORE`s are genuinely cold there, each charging
`gasColdSload` above its value case.  This variant reads its three keys in
the temporal convention, stores the hole and the moved index through
`temporal_sstore_cold_runCompiled`, and takes two non-membership hypotheses
at the entry state in their place.  Fixed charge `139 = 439 - 300` plus the
two explicit `gasColdSload` surcharges. -/

private theorem not_mem_hashSet_insert {α : Type _} [BEq α] [Hashable α]
    [LawfulBEq α] {s : Std.HashSet α} {x p : α}
    (h : p ∉ s) (hne : x ≠ p) : p ∉ s.insert x := by
  intro hmem
  rcases Std.HashSet.mem_insert.mp hmem with he | hx
  · exact hne (eq_of_beq he)
  · exact h hx

private theorem addAccessedStorageKey_getStorVal (devm : Devm) (a : Adr)
    (k : B256) (a' : Adr) (key : B256) :
    (addAccessedStorageKey devm a k).getStorVal a' key =
      devm.getStorVal a' key := rfl

private theorem addAccessedStorageKey_accessedStorageKeys (devm : Devm)
    (a : Adr) (k : B256) :
    (addAccessedStorageKey devm a k).accessedStorageKeys =
      devm.accessedStorageKeys.insert (a, k) := rfl

private theorem not_mem_temporalSloadBase {sevm : Sevm} {base : Devm}
    {readKey : B256} {p : Adr × B256}
    (h : p ∉ base.accessedStorageKeys)
    (hne : (sevm.currentTarget, readKey) ≠ p) :
    p ∉ (temporalSloadBase sevm base readKey).accessedStorageKeys := by
  unfold temporalSloadBase
  split
  · exact h
  · exact not_mem_hashSet_insert h hne

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem removeTarget_swapPop_toFinish_coldEntry_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (idxSloadCost lenSloadCost arrSloadCost holeCost movedIndexCost
      tailClearCost lengthRestoreCost indexClearCost finishGas G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (htargetValid : nonzeroCanonicalAddress target)
    (hlastValid : canonicalAddress lastTarget)
    (hlastNe : lastTarget ≠ target)
    (hidxNonzero : idx ≠ 0) (hidxBound : idx.toNat < 2 ^ 252)
    (hlenNonzero : len ≠ 0) (hlenBound : len.toNat < 2 ^ 252)
    (hidxNeLen : idx ≠ len)
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
    (hhole : base.getStorVal sevm.currentTarget
      (arrayEntrySlot idx) = holeCurrent)
    (hmoved : base.getStorVal sevm.currentTarget
      (indexSlot lastTarget) = movedCurrent)
    (htail : base.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = idx)
    (hlength : base.getStorVal sevm.currentTarget
      arrayLengthSlot = len)
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
    (hidxSloadCost : temporalSloadCost sevm base (indexSlot target) =
      idxSloadCost)
    (hlenSloadCost : temporalSloadCost sevm
      (temporalSloadBase sevm base (indexSlot target)) arrayLengthSlot =
      lenSloadCost)
    (harrSloadCost : temporalSloadCost sevm
      (temporalSloadBase sevm
        (temporalSloadBase sevm base (indexSlot target)) arrayLengthSlot)
      (arrayEntrySlot len) = arrSloadCost)
    (hholeCold : (sevm.currentTarget, arrayEntrySlot idx) ∉
      base.accessedStorageKeys)
    (hmovedCold : (sevm.currentTarget, indexSlot lastTarget) ∉
      base.accessedStorageKeys)
    (hholeCost : sstoreValueCost holeOriginal holeCurrent lastTarget =
      holeCost)
    (hmovedIndexCost : sstoreValueCost movedOriginal movedCurrent idx =
      movedIndexCost)
    (htailClearCost : sstoreValueCost tailOriginal lastTarget 0 =
      tailClearCost)
    (hlengthRestoreCost : sstoreValueCost lengthOriginal len oldLength =
      lengthRestoreCost)
    (hindexClearCost : sstoreValueCost indexOriginal idx 0 =
      indexClearCost)
    (hsub : len - 1 = oldLength)
    (hgasFinal : gCallStipend < G + finishGas + 12 + indexClearCost)
    (hstatic : sevm.isStatic = false)
    (post : Devm)
    (hfinish :
      let coldBase := temporalSloadBase sevm
        (temporalSloadBase sevm
          (temporalSloadBase sevm base (indexSlot target)) arrayLengthSlot)
        (arrayEntrySlot len)
      let holePost := temporalSstorePost sevm
        (addAccessedStorageKey coldBase sevm.currentTarget
          (arrayEntrySlot idx)) (arrayEntrySlot idx) lastTarget
      let movedPost := temporalSstorePost sevm
        (addAccessedStorageKey holePost sevm.currentTarget
          (indexSlot lastTarget)) (indexSlot lastTarget) idx
      let tailPost := temporalSstorePost sevm movedPost (arrayEntrySlot len) 0
      let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
      let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
      let MLast := MLength.write (lastTargetWord * 32).toNat
        lastTarget.toBytes
      let removePost := indexClearPost sevm tailPost target oldLength
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, MLast, G + finishGas⟩)
        finishSetPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 139 + lastExtCost + indexExtCost + lengthExtCost +
          idxSloadCost + lenSloadCost + arrSloadCost + gasColdSload +
          gasColdSload + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost⟩)
      removeTarget post := by
  dsimp only at hfinish
  let holeKey := arrayEntrySlot idx
  let movedKey := indexSlot lastTarget
  let tailKey := arrayEntrySlot len
  let indexKey := indexSlot target
  let base1 := temporalSloadBase sevm base (indexSlot target)
  let base2 := temporalSloadBase sevm base1 arrayLengthSlot
  let base3 := temporalSloadBase sevm base2 (arrayEntrySlot len)
  let holePost := temporalSstorePost sevm
    (addAccessedStorageKey base3 sevm.currentTarget (arrayEntrySlot idx))
    (arrayEntrySlot idx) lastTarget
  let movedPost := temporalSstorePost sevm
    (addAccessedStorageKey holePost sevm.currentTarget
      (indexSlot lastTarget)) (indexSlot lastTarget) idx
  let tailPost := temporalSstorePost sevm movedPost (arrayEntrySlot len) 0
  let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    lastTarget.toBytes
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have hmovedHole : movedKey ≠ holeKey := by
    simpa only [movedKey, holeKey] using
      (registryAddressFamilies_ne_arrayEntrySlot
        hlastValid hlastValid hidxBound).2.1
  have hmovedTailNe : movedKey ≠ tailKey := by
    simpa only [movedKey, tailKey] using
      (registryAddressFamilies_ne_arrayEntrySlot
        hlastValid hlastValid hlenBound).2.1
  have hindexHoleNe : indexKey ≠ holeKey := by
    simpa only [indexKey, holeKey] using
      (registryAddressFamilies_ne_arrayEntrySlot
        htargetValid.2 htargetValid.2 hidxBound).2.1
  have hindexTailNe : indexKey ≠ tailKey := by
    simpa only [indexKey, tailKey] using
      (registryAddressFamilies_ne_arrayEntrySlot
        htargetValid.2 htargetValid.2 hlenBound).2.1
  have hindexMovedNe : indexKey ≠ movedKey := by
    intro h
    exact hlastNe (indexSlot_injective hlastValid htargetValid.2 h.symm)
  have hindexLength : indexKey ≠ arrayLengthSlot := by
    simpa only [indexKey] using
      (registryAddressFamilies_ne_arrayLengthSlot
        htargetValid.2 htargetValid.2).2.1
  have hmovedLength : movedKey ≠ arrayLengthSlot := by
    simpa only [movedKey] using
      (registryAddressFamilies_ne_arrayLengthSlot
        hlastValid hlastValid).2.1
  have hlengthHole : arrayLengthSlot ≠ holeKey := by
    simpa only [holeKey] using
      arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hidxNonzero hidxBound
  have hlengthTailNe : arrayLengthSlot ≠ tailKey := by
    simpa only [tailKey] using
      arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hlenNonzero hlenBound
  have htailHole : tailKey ≠ holeKey := by
    intro h
    exact hidxNeLen
      (slot_injective_payload (region := arrayRegion)
        (by norm_num [arrayRegion]) hlenBound hidxBound
        (by simpa only [tailKey, holeKey, arrayEntrySlot] using h)).symm
  -- the three reads' values and the two cold write keys, at the threaded base
  have hhole3 : base3.getStorVal sevm.currentTarget holeKey = holeCurrent := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot len)).getStorVal sevm.currentTarget holeKey =
      holeCurrent
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget holeKey = holeCurrent
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget holeKey = holeCurrent
    rw [temporalSloadBase_getStorVal]
    exact hhole
  have htail3 : base3.getStorVal sevm.currentTarget tailKey = lastTarget := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot len)).getStorVal sevm.currentTarget tailKey = lastTarget
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget tailKey = lastTarget
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget tailKey = lastTarget
    rw [temporalSloadBase_getStorVal]
    exact htail
  have hindex3 : base3.getStorVal sevm.currentTarget indexKey = idx := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot len)).getStorVal sevm.currentTarget indexKey = idx
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget indexKey = idx
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget indexKey = idx
    rw [temporalSloadBase_getStorVal]
    exact hindex
  have hmoved3 : base3.getStorVal sevm.currentTarget movedKey =
      movedCurrent := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot len)).getStorVal sevm.currentTarget movedKey =
      movedCurrent
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget movedKey = movedCurrent
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget movedKey =
      movedCurrent
    rw [temporalSloadBase_getStorVal]
    exact hmoved
  have hlength3 : base3.getStorVal sevm.currentTarget arrayLengthSlot =
      len := by
    show (temporalSloadBase sevm base2
      (arrayEntrySlot len)).getStorVal sevm.currentTarget arrayLengthSlot =
      len
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget arrayLengthSlot = len
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget arrayLengthSlot = len
    rw [temporalSloadBase_getStorVal]
    exact hlength
  have hholeCold3 : (sevm.currentTarget, holeKey) ∉
      base3.accessedStorageKeys :=
    not_mem_temporalSloadBase
      (not_mem_temporalSloadBase
        (not_mem_temporalSloadBase hholeCold (pairNe hindexHoleNe))
        (pairNe hlengthHole))
      (pairNe htailHole)
  have hmovedCold3 : (sevm.currentTarget, movedKey) ∉
      base3.accessedStorageKeys :=
    not_mem_temporalSloadBase
      (not_mem_temporalSloadBase
        (not_mem_temporalSloadBase hmovedCold (pairNe hindexMovedNe))
        (pairNe hmovedLength.symm))
      (pairNe hmovedTailNe.symm)
  have hmovedColdHole : (sevm.currentTarget, movedKey) ∉
      holePost.accessedStorageKeys := by
    rw [show holePost = temporalSstorePost sevm
      (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
      lastTarget from rfl,
      temporalSstorePost_accessedStorageKeys,
      addAccessedStorageKey_accessedStorageKeys]
    exact not_mem_hashSet_insert hmovedCold3 (pairNe hmovedHole.symm)
  -- values across the write tower
  have hmovedHolePost : holePost.getStorVal sevm.currentTarget movedKey =
      movedCurrent := by
    rw [show holePost = temporalSstorePost sevm
      (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
      lastTarget from rfl,
      temporalSstorePost_other sevm _ holeKey lastTarget
        sevm.currentTarget movedKey (pairNe hmovedHole),
      addAccessedStorageKey_getStorVal]
    exact hmoved3
  have htailMovedPost : movedPost.getStorVal sevm.currentTarget tailKey =
      lastTarget := by
    rw [show movedPost = temporalSstorePost sevm
      (addAccessedStorageKey holePost sevm.currentTarget movedKey) movedKey
      idx from rfl,
      temporalSstorePost_other sevm _ movedKey idx
        sevm.currentTarget tailKey (pairNe hmovedTailNe.symm),
      addAccessedStorageKey_getStorVal,
      show holePost = temporalSstorePost sevm
        (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
        lastTarget from rfl,
      temporalSstorePost_other sevm _ holeKey lastTarget
        sevm.currentTarget tailKey (pairNe htailHole),
      addAccessedStorageKey_getStorVal]
    exact htail3
  have hlengthTailPost : tailPost.getStorVal sevm.currentTarget
      arrayLengthSlot = len := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 from rfl,
      temporalSstorePost_other sevm movedPost tailKey 0
        sevm.currentTarget arrayLengthSlot (pairNe hlengthTailNe),
      show movedPost = temporalSstorePost sevm
        (addAccessedStorageKey holePost sevm.currentTarget movedKey) movedKey
        idx from rfl,
      temporalSstorePost_other sevm _ movedKey idx
        sevm.currentTarget arrayLengthSlot (pairNe hmovedLength.symm),
      addAccessedStorageKey_getStorVal,
      show holePost = temporalSstorePost sevm
        (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
        lastTarget from rfl,
      temporalSstorePost_other sevm _ holeKey lastTarget
        sevm.currentTarget arrayLengthSlot (pairNe hlengthHole),
      addAccessedStorageKey_getStorVal]
    exact hlength3
  have hindexTailPost : tailPost.getStorVal sevm.currentTarget indexKey =
      idx := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 from rfl,
      temporalSstorePost_other sevm movedPost tailKey 0
        sevm.currentTarget indexKey (pairNe hindexTailNe),
      show movedPost = temporalSstorePost sevm
        (addAccessedStorageKey holePost sevm.currentTarget movedKey) movedKey
        idx from rfl,
      temporalSstorePost_other sevm _ movedKey idx
        sevm.currentTarget indexKey (pairNe hindexMovedNe),
      addAccessedStorageKey_getStorVal,
      show holePost = temporalSstorePost sevm
        (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
        lastTarget from rfl,
      temporalSstorePost_other sevm _ holeKey lastTarget
        sevm.currentTarget indexKey (pairNe hindexHoleNe),
      addAccessedStorageKey_getStorVal]
    exact hindex3
  -- warmth across the write tower
  have hwarmTailMoved : (sevm.currentTarget, tailKey) ∈
      movedPost.accessedStorageKeys := by
    rw [show movedPost = temporalSstorePost sevm
      (addAccessedStorageKey holePost sevm.currentTarget movedKey) movedKey
      idx from rfl,
      temporalSstorePost_accessedStorageKeys,
      addAccessedStorageKey_accessedStorageKeys,
      show holePost = temporalSstorePost sevm
        (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
        lastTarget from rfl,
      temporalSstorePost_accessedStorageKeys,
      addAccessedStorageKey_accessedStorageKeys]
    exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (temporalSloadBase_warm sevm base2 (arrayEntrySlot len)))))
  have hwarmLengthTail : (sevm.currentTarget, arrayLengthSlot) ∈
      tailPost.accessedStorageKeys := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 from rfl,
      temporalSstorePost_accessedStorageKeys,
      show movedPost = temporalSstorePost sevm
        (addAccessedStorageKey holePost sevm.currentTarget movedKey) movedKey
        idx from rfl,
      temporalSstorePost_accessedStorageKeys,
      addAccessedStorageKey_accessedStorageKeys,
      show holePost = temporalSstorePost sevm
        (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
        lastTarget from rfl,
      temporalSstorePost_accessedStorageKeys,
      addAccessedStorageKey_accessedStorageKeys]
    exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (temporalSloadBase_preserves_warm sevm base2
        (arrayEntrySlot len) _
        (temporalSloadBase_warm sevm base1 arrayLengthSlot)))))
  have hwarmIndexTail : (sevm.currentTarget, indexKey) ∈
      tailPost.accessedStorageKeys := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 from rfl,
      temporalSstorePost_accessedStorageKeys,
      show movedPost = temporalSstorePost sevm
        (addAccessedStorageKey holePost sevm.currentTarget movedKey) movedKey
        idx from rfl,
      temporalSstorePost_accessedStorageKeys,
      addAccessedStorageKey_accessedStorageKeys,
      show holePost = temporalSstorePost sevm
        (addAccessedStorageKey base3 sevm.currentTarget holeKey) holeKey
        lastTarget from rfl,
      temporalSstorePost_accessedStorageKeys,
      addAccessedStorageKey_accessedStorageKeys]
    exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (temporalSloadBase_preserves_warm sevm base2
        (arrayEntrySlot len) _
        (temporalSloadBase_preserves_warm sevm base1 arrayLengthSlot _
          (temporalSloadBase_warm sevm base (indexSlot target)))))))
  -- the staged image
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
  have htargetLast : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target :=
    ((sliceBeforeLast (by decide)).trans
      ((sliceBeforeLength (by decide)).trans
        (sliceBeforeIndex (by decide)))).trans htarget
  have hremovedLength : Bytes.toB256
      (imgLength.sliceD (removedIndexWord * 32).toNat 32 0) = idx := by
    rw [sliceBeforeLength (word := removedIndexWord) (by decide)]
    dsimp only [imgIndex]
    rw [show 32 = idx.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hremovedLast : Bytes.toB256
      (imgLast.sliceD (removedIndexWord * 32).toNat 32 0) = idx :=
    (sliceBeforeLast (word := removedIndexWord) (by decide)).trans
      hremovedLength
  have hlengthLast : Bytes.toB256
      (imgLast.sliceD (arrayLengthWord * 32).toNat 32 0) = len := by
    rw [sliceBeforeLast (word := arrayLengthWord) (by decide)]
    dsimp only [imgLength]
    rw [show 32 = len.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hlastLast : Bytes.toB256
      (imgLast.sliceD (lastTargetWord * 32).toNat 32 0) = lastTarget := by
    dsimp only [imgLast]
    rw [show 32 = lastTarget.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hMLastCovered (word : B256)
      (hoff : (word * 32).toNat + 32 ≤ 736) :
      (word * 32).toNat + 32 ≤ MLast.size := by
    rw [hsizeLast]
    omega
  have readMemoryLast (word : B256)
      (hoff : (word * 32).toNat + 32 ≤ 736) :
      (MLast.read (word * 32).toNat 32).2 = MLast := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halignLast
      (hMLastCovered word hoff))]
  have readValueLast (word value : B256)
      (hvalue : Bytes.toB256
        (imgLast.sliceD (word * 32).toNat 32 0) = value) :
      (MLast.read (word * 32).toNat 32).1.toB256 = value := by
    rw [Mem.Reads.read hreadsLast]
    exact hvalue
  have hremovedMemory := readMemoryLast removedIndexWord (by decide)
  have hlengthMemory := readMemoryLast arrayLengthWord (by decide)
  have hlastMemory := readMemoryLast lastTargetWord (by decide)
  have hremovedValue := readValueLast removedIndexWord idx hremovedLast
  have hlengthValue := readValueLast arrayLengthWord len hlengthLast
  have hlastValue := readValueLast lastTargetWord lastTarget hlastLast
  -- the restore tail at the tail-cleared state
  have hrestore := removeTarget_restoreTail_runCompiled
    dp sevm tailPost MLast imgLast target oldLength len idx 0 stack hstack
    lengthOriginal indexOriginal lengthRestoreCost indexClearCost finishGas G
    hreadsLast htargetLast hlengthLast htargetValid
    (by rw [hsizeLast]; exact Nat.le_max_right _ _) halignLast
    hlengthTailPost hindexTailPost hlengthOrig hindexOrig
    hlengthRestoreCost hindexClearCost hwarmLengthTail hwarmIndexTail hsub
    hgasFinal hstatic post
    (by
      dsimp only
      exact hfinish)
  let fs := (runtime dp).main :: (runtime dp).aux
  have hrestore' : Func.RunCompiled fs sevm
      (tailPost.setMach
        ⟨stack, MLast,
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
        ⟨tailKey :: 0 :: stack, MLast,
          G + finishGas + 44 + lengthRestoreCost + indexClearCost +
            tailClearCost⟩)
      (Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled htailMovedPost htailOrig htailClearCost
        hwarmTailMoved (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      hrestore'
  have htailTag : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨len :: 0 :: stack, MLast,
          G + finishGas + 50 + lengthRestoreCost + indexClearCost +
            tailClearCost⟩)
      (tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [tailKey]
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
        ⟨0 :: stack, MLast,
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
      rw [Devm.extCost_zero_of_le halignLast
        (hMLastCovered arrayLengthWord (by decide))]
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
        ⟨stack, MLast,
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
        ⟨movedKey :: idx :: stack, MLast,
          G + finishGas + 58 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost⟩)
      (Ninst.sstore ::: pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord arrayLengthWord +++
        pushB256 1 ::: swap 0 ::: sub ::: pushB256 arrayLengthSlot :::
        Ninst.sstore ::: pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_cold_runCompiled hmovedHolePost hmovedOrig
        hmovedIndexCost hmovedColdHole
        (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      htailPrefix
  have hmovedTag : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨lastTarget :: idx :: stack, MLast,
          G + finishGas + 64 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost⟩)
      (tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [movedKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 64 + lengthRestoreCost + indexClearCost +
          tailClearCost + gasColdSload + movedIndexCost - 6 =
          G + finishGas + 58 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost := by omega
      rw [hg]
      exact hstoreMoved
  have hmovedLast : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨idx :: stack, MLast,
          G + finishGas + 70 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost⟩)
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
      rw [Devm.extCost_zero_of_le halignLast
        (hMLastCovered lastTargetWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlastValue, hlastMemory]
      have hg : G + finishGas + 70 + lengthRestoreCost + indexClearCost +
          tailClearCost + gasColdSload + movedIndexCost - 6 =
          G + finishGas + 64 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost := by omega
      rw [hg]
      exact hmovedTag
  have hmovedPrefix : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨stack, MLast,
          G + finishGas + 76 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost⟩)
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
      rw [Devm.extCost_zero_of_le halignLast
        (hMLastCovered removedIndexWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hremovedValue, hremovedMemory]
      have hg : G + finishGas + 76 + lengthRestoreCost + indexClearCost +
          tailClearCost + gasColdSload + movedIndexCost - 6 =
          G + finishGas + 70 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost := by omega
      rw [hg]
      exact hmovedLast
  have hstoreHole : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨holeKey :: lastTarget :: stack, MLast,
          G + finishGas + 76 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
            holeCost⟩)
      (Ninst.sstore ::: loadWord removedIndexWord +++
        loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_cold_runCompiled hhole3 hholeOrig hholeCost hholeCold3
        (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      hmovedPrefix
  have hholeTag : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨idx :: lastTarget :: stack, MLast,
          G + finishGas + 82 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
            holeCost⟩)
      (tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    func_run (2) [holeKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 82 + lengthRestoreCost + indexClearCost +
          tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
          holeCost - 6 =
          G + finishGas + 76 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
            holeCost := by omega
      rw [hg]
      exact hstoreHole
  have hholeRemoved : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨lastTarget :: stack, MLast,
          G + finishGas + 88 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
            holeCost⟩)
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
      rw [Devm.extCost_zero_of_le halignLast
        (hMLastCovered removedIndexWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hremovedValue, hremovedMemory]
      have hg : G + finishGas + 88 + lengthRestoreCost + indexClearCost +
          tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
          holeCost - 6 =
          G + finishGas + 82 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
            holeCost := by omega
      rw [hg]
      exact hholeTag
  have hholePrefix : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨stack, MLast,
          G + finishGas + 94 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
            holeCost⟩)
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
      rw [Devm.extCost_zero_of_le halignLast
        (hMLastCovered lastTargetWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlastValue, hlastMemory]
      have hg : G + finishGas + 94 + lengthRestoreCost + indexClearCost +
          tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
          holeCost - 6 =
          G + finishGas + 88 + lengthRestoreCost + indexClearCost +
            tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
            holeCost := by omega
      rw [hg]
      exact hholeRemoved
  -- the store suffix entered from the third read, at the staged image
  have hstores : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨stack, MLast,
          G + finishGas + 94 + gasColdSload + gasColdSload + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
      (loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    have hg : G + finishGas + 94 + gasColdSload + gasColdSload + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost =
        G + finishGas + 94 + lengthRestoreCost + indexClearCost +
          tailClearCost + gasColdSload + movedIndexCost + gasColdSload +
          holeCost := by omega
    rw [hg]
    simpa only [lastTargetIndexKey, prepend_append] using hholePrefix
  -- values at the intermediate read bases
  have hlength1 : base1.getStorVal sevm.currentTarget arrayLengthSlot =
      len := by
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget arrayLengthSlot = len
    rw [temporalSloadBase_getStorVal]
    exact hlength
  have htail2 : base2.getStorVal sevm.currentTarget
      (arrayEntrySlot len) = lastTarget := by
    show (temporalSloadBase sevm base1
      arrayLengthSlot).getStorVal sevm.currentTarget (arrayEntrySlot len) =
      lastTarget
    rw [temporalSloadBase_getStorVal]
    show (temporalSloadBase sevm base
      (indexSlot target)).getStorVal sevm.currentTarget (arrayEntrySlot len) =
      lastTarget
    rw [temporalSloadBase_getStorVal]
    exact htail
  -- the staged reads the prefix performs
  have hlengthValueMid :
      (MLength.read (arrayLengthWord * 32).toNat 32).1.toB256 = len := by
    rw [Mem.Reads.read hreadsLength]
    dsimp only [imgLength]
    rw [show 32 = len.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hlengthMemoryMid :
      (MLength.read (arrayLengthWord * 32).toNat 32).2 = MLength := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halignLength (by
      rw [hsizeLength, show (arrayLengthWord * 32).toNat + 32 = 704 by decide]
      exact Nat.le_max_right _ _))]
  have hsaveLast : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨lastTargetWord * 32 :: lastTarget :: stack, MLength,
          G + finishGas + 97 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
        (G := G + finishGas + 94 + gasColdSload + gasColdSload + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost) (M := MLast) rfl
        (Devm.extCost_of_size
          (i := (lastTargetWord * 32).toNat) (sz := 32) (e := lastExtCost)
          hsizeLength hlastExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · simpa only [fs, MLast, Devm.setMach_setMach,
        Devm.memory_setMach] using hstores
  have hlastLoad : Func.RunCompiled fs sevm
      (base3.setMach
        ⟨lastTarget :: stack, MLength,
          G + finishGas + 100 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      have hg : G + finishGas + 100 + lastExtCost + gasColdSload +
          gasColdSload + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 3 =
          G + finishGas + 97 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hsaveLast
  have harrSloadStep : Ninst.RunCompiled sevm
      (base2.setMach
        ⟨tailKey :: stack, MLength,
          G + finishGas + 100 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost⟩)
      Ninst.sload
      (base3.setMach
        ⟨lastTarget :: stack, MLength,
          G + finishGas + 100 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := base2)
      (key := arrayEntrySlot len) (value := lastTarget) (stack := stack)
      (M := MLength)
      (G := G + finishGas + 100 + lastExtCost + gasColdSload + gasColdSload +
        holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost)
      htail2 (by omega)
    rw [show temporalSloadCost sevm base2 (arrayEntrySlot len) =
      arrSloadCost from harrSloadCost] at h
    exact h
  have hloadLastStorage : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨tailKey :: stack, MLength,
          G + finishGas + 100 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost⟩)
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
        ⟨len :: stack, MLength,
          G + finishGas + 106 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost⟩)
      (tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    func_run (2) [tailKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      have hg : G + finishGas + 106 + lastExtCost + gasColdSload +
          gasColdSload + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost + arrSloadCost - 6 =
          G + finishGas + 100 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost := by omega
      rw [hg]
      exact hloadLastStorage
  have hlastPrefix : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨stack, MLength,
          G + finishGas + 112 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost⟩)
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
      rw [hlengthValueMid, hlengthMemoryMid]
      have hg : G + finishGas + 112 + lastExtCost + gasColdSload +
          gasColdSload + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost + arrSloadCost - 6 =
          G + finishGas + 106 + lastExtCost + gasColdSload + gasColdSload +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost + arrSloadCost := by omega
      rw [hg]
      exact hlastTag
  have hsaveLength : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨arrayLengthWord * 32 :: len :: stack, MIndex,
          G + finishGas + 115 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost⟩)
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
        (G := G + finishGas + 112 + lastExtCost + gasColdSload +
          gasColdSload + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost + arrSloadCost)
        (M := MLength) rfl
        (Devm.extCost_of_size
          (i := (arrayLengthWord * 32).toNat) (sz := 32) (e := lengthExtCost)
          hsizeIndex hlengthExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlastPrefix
  have hsaveLengthPrefix : Func.RunCompiled fs sevm
      (base2.setMach
        ⟨len :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost⟩)
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
      have hg : G + finishGas + 118 + lastExtCost + lengthExtCost +
          gasColdSload + gasColdSload + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost +
          arrSloadCost - 3 =
          G + finishGas + 115 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost := by omega
      rw [hg]
      exact hsaveLength
  have hlenSloadStep : Ninst.RunCompiled sevm
      (base1.setMach
        ⟨arrayLengthSlot :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost +
            lenSloadCost⟩)
      Ninst.sload
      (base2.setMach
        ⟨len :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := base1)
      (key := arrayLengthSlot) (value := len) (stack := stack)
      (M := MIndex)
      (G := G + finishGas + 118 + lastExtCost + lengthExtCost +
        gasColdSload + gasColdSload + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost + arrSloadCost)
      hlength1 (by omega)
    rw [show temporalSloadCost sevm base1 arrayLengthSlot =
      lenSloadCost from hlenSloadCost] at h
    exact h
  have hlengthLoad : Func.RunCompiled fs sevm
      (base1.setMach
        ⟨arrayLengthSlot :: stack, MIndex,
          G + finishGas + 118 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost +
            lenSloadCost⟩)
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
          G + finishGas + 121 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost +
            lenSloadCost⟩)
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
      have hg : G + finishGas + 121 + lastExtCost + lengthExtCost +
          gasColdSload + gasColdSload + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost + arrSloadCost +
          lenSloadCost - 3 =
          G + finishGas + 118 + lastExtCost + lengthExtCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost + arrSloadCost +
            lenSloadCost := by omega
      rw [hg]
      exact hlengthLoad
  have hsaveIndex : Func.RunCompiled fs sevm
      (base1.setMach
        ⟨removedIndexWord * 32 :: idx :: stack, M,
          G + finishGas + 124 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost⟩)
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
        (G := G + finishGas + 121 + lastExtCost + lengthExtCost +
          gasColdSload + gasColdSload + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost + arrSloadCost +
          lenSloadCost)
        (M := MIndex) rfl
        (Devm.extCost_of_size
          (i := (removedIndexWord * 32).toNat) (sz := 32) (e := indexExtCost)
          hsize hindexExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlengthPrefix
  have hsaveIndexPrefix : Func.RunCompiled fs sevm
      (base1.setMach
        ⟨idx :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost⟩)
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
          lengthExtCost + gasColdSload + gasColdSload + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost + arrSloadCost + lenSloadCost - 3 =
          G + finishGas + 124 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost := by omega
      rw [hg]
      exact hsaveIndex
  have hidxSloadStep : Ninst.RunCompiled sevm
      (base.setMach
        ⟨indexKey :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost + idxSloadCost⟩)
      Ninst.sload
      (base1.setMach
        ⟨idx :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := base)
      (key := indexSlot target) (value := idx) (stack := stack)
      (M := M)
      (G := G + finishGas + 127 + lastExtCost + indexExtCost +
        lengthExtCost + gasColdSload + gasColdSload + holeCost +
        movedIndexCost + tailClearCost + lengthRestoreCost +
        indexClearCost + arrSloadCost + lenSloadCost)
      hindex (by omega)
    rw [show temporalSloadCost sevm base (indexSlot target) =
      idxSloadCost from hidxSloadCost] at h
    exact h
  have hindexLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨indexKey :: stack, M,
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost + idxSloadCost⟩)
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
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost + idxSloadCost⟩)
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
          lengthExtCost + gasColdSload + gasColdSload + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost + arrSloadCost + lenSloadCost + idxSloadCost - 6 =
          G + finishGas + 127 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost + idxSloadCost := by omega
      rw [hg]
      exact hindexLoad
  have hindexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, M,
          G + finishGas + 139 + lastExtCost + indexExtCost + lengthExtCost +
            idxSloadCost + lenSloadCost + arrSloadCost + gasColdSload +
            gasColdSload + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
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
          gasColdSload + gasColdSload + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost - 6 =
          G + finishGas + 133 + lastExtCost + indexExtCost + lengthExtCost +
            gasColdSload + gasColdSload + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost +
            arrSloadCost + lenSloadCost + idxSloadCost := by omega
      rw [hg]
      exact hindexTag
  simp only [removeTarget]
  simpa only [fs, MLast] using hindexPrefix

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
