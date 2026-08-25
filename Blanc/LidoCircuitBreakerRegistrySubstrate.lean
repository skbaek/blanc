import Blanc.LidoCircuitBreakerAccess

/-!
Shared substrate for the Lido CircuitBreaker registration transitions.

This leaf carries what every registration chronology needs: the temporal
SLOAD/SSTORE transition layer, the scratch-word prepend lemmas, the generalized
swap-pop removal walk, the chronology-independent `finishSetPauser` and
`afterOldPauser` glue, the shared `setPauserKernel` prefixes for the append and
the found arms, the shared `registerAfterSet` old-last prefix and
nonzero-new-pauser suffix, and the dispatch and settlement scaffolding.

Nothing here is specific to one chronology.  A declaration that mentions a
chronology in its name belongs in that chronology's leaf, not in this file.  A
branch condition is not a chronology: `append`, `found`, `foundNonzero` and
`oldLast` each name an arm that two chronologies reach, which is why their walks
live here.

Declarations named `entryWritePost`, `indexWritePost`, `entryClearPost`,
`lengthWritePost` and `indexClearPost` form a nested `temporalSstorePost`
tower.  Each has one-layer transport lemmas over an abstract base; use those by
`rw` rather than crossing a tower by `exact`, `change` or `rfl`, and never drop
a name from a working `simp only` set over them.  See README.md,
*Proof-performance conventions: defeq and wide-recursion state towers*.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst


theorem Bytes.sliceD_writeAt_after
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt, if_neg]
  omega

/-- Writing one word at memory offset `0` — the event-payload scratch slot every
`registerAfterSet` expiry arm uses — leaves the new-pauser scratch word intact,
because word 17 starts far past the first 32 bytes. -/
private theorem readNewPauser_after_writeZero
    {M : Mem} {bs : Bytes} {w : B256}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs) :
    ((M.write 0 w.toBytes).read
      (newPauserWord * 32).toNat 32).1 =
      (M.read (newPauserWord * 32).toNat 32).1 := by
  rw [Mem.Reads.read (Mem.Reads.write hwf hreads 0 w.toBytes),
    Mem.Reads.read hreads, List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  rw [Bytes.getD_writeAt, if_neg]
  have hi' := List.mem_range.mp hi
  rw [B256.length_toBytes]
  have hoff : 32 ≤ (newPauserWord * 32).toNat := by decide
  omega

/-- A one-word write at offset `0` cannot grow a memory that already covers its
first word. -/
private theorem size_writeZero_word_of_le
    {M : Mem} {w : B256} (h : 32 ≤ M.size) :
    (M.write 0 w.toBytes).size = M.size := by
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp)
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, hlen, Nat.zero_add]
    rw [if_pos h]
    split <;> rfl

theorem addAccessedStorageKey_setMach_setMach
    {base : Devm} {target : Adr} {key : B256} {m m' : Mach} :
    (addAccessedStorageKey (base.setMach m) target key).setMach m' =
      (addAccessedStorageKey base target key).setMach m' := rfl

private theorem accessedStorageKeys_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedStorageKeys = base.accessedStorageKeys := rfl

theorem refundCounter_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).refundCounter = base.refundCounter := rfl

def temporalSloadBase (sevm : Sevm) (base : Devm)
    (key : B256) : Devm :=
  if (sevm.currentTarget, key) ∈ base.accessedStorageKeys then base
  else addAccessedStorageKey base sevm.currentTarget key

def temporalSloadCost (sevm : Sevm) (base : Devm)
    (key : B256) : Nat :=
  if (sevm.currentTarget, key) ∈ base.accessedStorageKeys then gasWarmAccess
  else gasColdSload

def temporalSstorePost (sevm : Sevm) (base : Devm)
    (key value : B256) : Devm :=
  (base.withRefundCounter (sstoreNewRefundCounter value
    (getOrigStorVal sevm sevm.currentTarget key)
    (base.getStorVal sevm.currentTarget key) base.refundCounter)).setStorVal
      sevm.currentTarget key value

theorem temporal_sload_runCompiled
    {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {M : Mem} {G : Nat}
    (hvalue : base.getStorVal sevm.currentTarget key = value)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨key :: stack, M,
        G + temporalSloadCost sevm base key⟩) Ninst.sload
      ((temporalSloadBase sevm base key).setMach
        ⟨value :: stack, M, G⟩) := by
  by_cases hwarm : (sevm.currentTarget, key) ∈ base.accessedStorageKeys
  · simp only [temporalSloadBase, temporalSloadCost, if_pos hwarm]
    exact Ninst.runCompiled_sload_warm rfl hwarm
      (by simpa only [Devm.getStorVal_setMach] using hvalue)
      (by simp only [Devm.gasLeft_setMach]) hroom
  · simp only [temporalSloadBase, temporalSloadCost, if_neg hwarm]
    simpa only [addAccessedStorageKey_setMach_setMach,
      Devm.memory_setMach] using
      Ninst.runCompiled_sload_cold
        (devm := base.setMach ⟨key :: stack, M, G + gasColdSload⟩)
        rfl (by simpa only [accessedStorageKeys_setMach] using hwarm)
        (by simpa only [Devm.getStorVal_setMach] using hvalue)
        (by simp only [Devm.gasLeft_setMach]) hroom

theorem temporal_sstore_runCompiled
    {sevm : Sevm} {base : Devm} {key value current original : B256}
    {stack : List B256} {M : Mem} {G cost : Nat}
    (hcurrent : base.getStorVal sevm.currentTarget key = current)
    (horiginal : getOrigStorVal sevm sevm.currentTarget key = original)
    (hcost : sstoreValueCost original current value = cost)
    (hwarm : (sevm.currentTarget, key) ∈ base.accessedStorageKeys)
    (hgas : gCallStipend < G + cost)
    (hstatic : sevm.isStatic = false) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨key :: value :: stack, M, G + cost⟩) Ninst.sstore
      ((temporalSstorePost sevm base key value).setMach
        ⟨stack, M, G⟩) := by
  apply Ninst.runCompiled_sstore_warm
      (c := cost) (G := G)
  · rfl
  · simpa only [accessedStorageKeys_setMach] using hwarm
  · simpa only [Devm.gasLeft_setMach] using hgas
  · exact hstatic
  · simp only [Devm.getStorVal_setMach, hcurrent, horiginal]
    exact hcost
  · simp only [Devm.getStorVal_setMach, refundCounter_setMach,
      hcurrent, horiginal]
  · simp only [Devm.gasLeft_setMach]

theorem temporalSloadBase_warm
    (sevm : Sevm) (base : Devm) (key : B256) :
    (sevm.currentTarget, key) ∈
      (temporalSloadBase sevm base key).accessedStorageKeys := by
  unfold temporalSloadBase
  split <;> rename_i h
  · exact h
  · exact Std.HashSet.mem_insert_self

theorem temporalSloadBase_getStorVal
    (sevm : Sevm) (base : Devm) (readKey : B256)
    (a : Adr) (key : B256) :
    (temporalSloadBase sevm base readKey).getStorVal a key =
      base.getStorVal a key := by
  unfold temporalSloadBase
  split <;> rfl

theorem temporalSloadBase_preserves_warm
    (sevm : Sevm) (base : Devm) (readKey key : B256)
    (h : (sevm.currentTarget, key) ∈ base.accessedStorageKeys) :
    (sevm.currentTarget, key) ∈
      (temporalSloadBase sevm base readKey).accessedStorageKeys := by
  unfold temporalSloadBase
  split
  · exact h
  · exact Std.HashSet.mem_insert.mpr (Or.inr h)

theorem temporalSloadBase_logs
    (sevm : Sevm) (base : Devm) (key : B256) :
    (temporalSloadBase sevm base key).logs = base.logs := by
  unfold temporalSloadBase
  split <;> rfl

theorem temporalSstorePost_other
    (sevm : Sevm) (base : Devm) (writeKey value : B256)
    (a : Adr) (key : B256)
    (hne : (a, key) ≠ (sevm.currentTarget, writeKey)) :
    (temporalSstorePost sevm base writeKey value).getStorVal a key =
      base.getStorVal a key := by
  by_cases ha : sevm.currentTarget = a
  · subst a
    have hk : writeKey ≠ key := fun h => hne (by rw [h])
    unfold temporalSstorePost
    show (Devm.getStor _ sevm.currentTarget).get key = _
    rw [setStorVal_getStor_self, Stor.get_set_ne _ hk]
    rfl
  · change (Devm.getStor _ a).get key = _
    simp only [temporalSstorePost, Devm.getStor, Devm.getAcct,
      Devm.setStorVal, Devm.withState, Devm.setWorld, State.setStorVal,
      Devm.state]
    rw [State.get_set_ne _ ha]
    rfl

theorem temporalSstorePost_self
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).getStorVal
      sevm.currentTarget key = value := by
  simp [temporalSstorePost, Devm.getStorVal, Devm.getAcct,
    Devm.setStorVal, Devm.withState, Devm.setWorld, State.setStorVal,
    Devm.state, State.get_set_self, Stor.get_set_self]

theorem temporalSstorePost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).accessedStorageKeys =
      base.accessedStorageKeys := rfl

theorem temporalSstorePost_logs
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).logs = base.logs := rfl

set_option maxRecDepth 16384 in
/-- Generic `finishSetPauser` walk, chronology-independent: reads the three
scratch words (`target`, `previousPauser`, `newPauser` — unconstrained), emits
the `LOG3` whose topics are exactly those words, reads the continuation word
(pinned to `0`, selecting the `registerAfterSet` arm; the pause arm is out of
scope), and takes the `registerAfterSet` continuation from the already-logged
state as a hypothesis.  Glue cost 1935 gas: 1900 for the loads and the `LOG3`,
9 for the continuation load and `iszero`, 14 for the branch pop, 12 for the
call burn. -/
theorem finishSetPauser_registerAfterSet_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target previousPauser newPauser : B256)
    (stack : List B256) (G : Nat) (post : Devm)
    (hstack : stack.length ≤ 1)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hstatic : sevm.isStatic = false)
    (hregister : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      ((base.addLog ⟨sevm.currentTarget,
          [pauserSetEvent, target, previousPauser, newPauser], []⟩).setMach
        ⟨stack, M, G⟩) registerAfterSet post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G + 1935⟩) finishSetPauser post := by
  let eventLog : Log :=
    ⟨sevm.currentTarget,
      [pauserSetEvent, target, previousPauser, newPauser], []⟩
  let eventBase := base.addLog eventLog
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hcontinuationCovered :
      (continuationWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (continuationWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have htargetMemory :
      (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have hpreviousMemory :
      (M.read (previousPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hpreviousCovered)]
  have hnewMemory :
      (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hcontinuationMemory :
      (M.read (continuationWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self
      (memExtSize_of_le halign hcontinuationCovered)]
  have htargetValue :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  have hpreviousValue :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 =
        previousPauser := by
    rw [Mem.Reads.read hreads]
    exact hprevious
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [Mem.Reads.read hreads]
    exact hnew
  have hcontinuationValue :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0 := by
    rw [Mem.Reads.read hreads]
    exact hcontinuation
  have hreadZero : M.read 0 0 = ([], M) := by
    simp [Mem.read, Mem.extend, memExtSize]
    rfl
  let fs := (runtime dp).main :: (runtime dp).aux
  have hlookup : fs[registerAfterSetSlot]? = some registerAfterSet := by
    simp [fs, runtime, aux, registerAfterSetSlot]
  have hcall : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨stack, M, G + 12⟩)
      (.call registerAfterSetSlot) post := by
    apply Func.RunCompiled.call hlookup
      (by simp only [Devm.stack_setMach]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := eventBase.setMach ⟨stack, M, G + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hregister
  have hbranch : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨1 :: stack, M, G + 26⟩)
      ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot)) post := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := eventBase.setMach ⟨1 :: stack, M, G + 26⟩)
          (x := (1 : B256)) (s := stack)
          (cost := gVerylow + gHigh + gJumpdest) (G := G + 12)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]))
    · exact hcall
  have hcontinuationRun : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨stack, M, G + 35⟩)
      (loadWord continuationWord +++ Ninst.iszero :::
        ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))) post := by
    func_run (3) [3]
    all_goals try ((try simp only [Devm.stack_setMach]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hcontinuationCovered]
      norm_num [gVerylow]
    case a =>
      rw [hcontinuationValue, hcontinuationMemory]
      norm_num
      exact hbranch
  simp only [finishSetPauser]
  func_run (10) [3, 3, 3, 1875]
  all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
  all_goals try simp_rw [hnewMemory]
  all_goals try simp_rw [hpreviousMemory]
  all_goals try simp_rw [htargetMemory]
  all_goals try {
    rw [Devm.extCost_zero_of_le halign (by omega)]
    norm_num [gVerylow, gLog, gLogdata, gLogtopic] }
  case h_cost =>
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    rw [Devm.extCost_zero_of_le halign (by omega)]
    norm_num [gLog, gLogdata, gLogtopic]
  case a =>
    rw [hnewValue, hpreviousValue, htargetValue]
    rw [show ((0 : B256) * 32).toNat = 0 by decide, hreadZero]
    exact hcontinuationRun

/-- Generic zero arm of `afterOldPauser`: the new-pauser scratch word is `0`,
so the walk branches to `removeTarget`, taken as a hypothesis.  Glue cost
35 gas: 9 for the memory read and `iszero`, 14 for the branch pop, 12 for the
call burn. -/
theorem afterOldPauser_removeTarget_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (stack : List B256) (G : Nat) (post : Devm)
    (hstack : stack.length ≤ 1)
    (hreads : Mem.Reads M img)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hsize : 576 ≤ M.size) (halign : M.size % 32 = 0)
    (hremove : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G⟩) removeTarget post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G + 35⟩) afterOldPauser post := by
  let fs := (runtime dp).main :: (runtime dp).aux
  have hlookup : fs[removeTargetSlot]? = some removeTarget := by
    simp [fs, runtime, aux, removeTargetSlot]
  have hcall : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 12⟩)
      (.call removeTargetSlot) post := by
    apply Func.RunCompiled.call hlookup (by
      simp only [Devm.stack_setMach]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := base.setMach ⟨stack, M, G + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hremove
  have hbranch : Func.RunCompiled fs sevm
      (base.setMach ⟨1 :: stack, M, G + 26⟩)
      ((.call removeTargetSlot) <?>
        (newCountKey +++ Ninst.sload ::: pushB256 1 ::: add :::
          newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot))
      post := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide) (by
      simp only [Devm.stack_setMach, List.length_cons]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := base.setMach ⟨1 :: stack, M, G + 26⟩)
          (x := (1 : B256)) (s := stack)
          (cost := gVerylow + gHigh + gJumpdest) (G := G + 12)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]))
    · exact hcall
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 = 576 := by decide
    omega
  have hnewMemory : (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  simp only [afterOldPauser]
  func_run (3) [3]
  all_goals try ((try simp only [Devm.stack_setMach]); omega)
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hnewCovered]
    norm_num [gVerylow]
  case a =>
    rw [Mem.Reads.read hreads, hnew, hnewMemory]
    have hg : G + 35 - 9 = G + 26 := by omega
    rw [hg]
    exact hbranch

/-- Generic nonzero arm of `afterOldPauser`: the new-pauser scratch word is
nonzero, so the walk loads the new count, increments and stores it, and calls
`finishSetPauser`, taken as a hypothesis from the count-updated state.  Glue
cost 64 gas above the count `SLOAD`/`SSTORE`: 9 for the memory read and
`iszero`, 13 for the branch pop, 12 + 12 for the two `newCountKey`
computations, 6 for the increment, 12 for the call burn.

Chronology-independent, so it lives here rather than in any leaf: the fresh,
absent and replacement chronologies all reach this arm. -/
theorem afterOldPauser_finishSetPauser_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (newPauser count nextCount countOriginal : B256)
    (stack : List B256) (countCost G : Nat) (post : Devm)
    (hstack : stack.length ≤ 1)
    (hreads : Mem.Reads M img)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hnewNonzero : newPauser ≠ 0)
    (hsize : 576 ≤ M.size) (halign : M.size % 32 = 0)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot newPauser) = count)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot newPauser) = countOriginal)
    (hcountNext : (1 : B256) + count = nextCount)
    (hcountCost : sstoreValueCost countOriginal count nextCount = countCost)
    (hgasStipend : gCallStipend < G + 12 + countCost)
    (hstatic : sevm.isStatic = false)
    (hfinish : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      ((temporalSstorePost sevm
          (temporalSloadBase sevm base (countSlot newPauser))
          (countSlot newPauser) nextCount).setMach ⟨stack, M, G⟩)
        finishSetPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + 64 + temporalSloadCost sevm base (countSlot newPauser) +
          countCost⟩) afterOldPauser post := by
  let countKey := countSlot newPauser
  let countBase := temporalSloadBase sevm base countKey
  let countPost := temporalSstorePost sevm countBase countKey nextCount
  have hcountBase : countBase.getStorVal sevm.currentTarget countKey =
      count := by
    simpa only [countBase, countKey, temporalSloadBase_getStorVal] using
      hcount
  have hwarmCount : (sevm.currentTarget, countKey) ∈
      countBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm base countKey
  let fs := (runtime dp).main :: (runtime dp).aux
  have hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser := by
    simp [fs, runtime, aux, finishSetPauserSlot]
  have hfinishCall : Func.RunCompiled fs sevm
      (countPost.setMach ⟨stack, M, G + 12⟩)
      (.call finishSetPauserSlot) post := by
    apply Func.RunCompiled.call hfinishLookup
      (by simp only [Devm.stack_setMach]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := countPost.setMach ⟨stack, M, G + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hfinish
  have hstoreCount : Func.RunCompiled fs sevm
      (countBase.setMach ⟨countKey :: nextCount :: stack, M,
        G + 12 + countCost⟩)
      (Ninst.sstore ::: .call finishSetPauserSlot) post := by
    apply Func.RunCompiled.next
    · exact temporal_sstore_runCompiled hcountBase hcountOrig hcountCost
        hwarmCount hgasStipend hstatic
    · exact hfinishCall
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 = 576 := by decide
    omega
  have hnewMemory : (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [Mem.Reads.read hreads]
    exact hnew
  have hcountKeyTail : Func.RunCompiled fs sevm
      (countBase.setMach ⟨nextCount :: stack, M, G + 24 + countCost⟩)
      (newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot) post := by
    func_run (4) [3, countKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    all_goals try {
      simpa [countKey, countSlot, slot] using
        congrArg (fun x : B256 => (regionWord countRegion).or x) hnewValue }
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow]
    case a =>
      rw [hnewMemory]
      have hg : G + 24 + countCost - 12 = G + 12 + countCost := by
        omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (countBase.setMach ⟨countKey :: nextCount :: stack, M,
          G + 12 + countCost⟩)
        (Ninst.sstore ::: .call finishSetPauserSlot) post
      exact hstoreCount
  have hcountTail : Func.RunCompiled fs sevm
      (countBase.setMach ⟨count :: stack, M, G + 30 + countCost⟩)
      (pushB256 1 ::: add ::: newCountKey +++
        Ninst.sstore ::: .call finishSetPauserSlot) post := by
    func_run (2)
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case a =>
      simp only
      rw [hcountNext]
      have hg : G + 30 + countCost - 6 = G + 24 + countCost := by
        omega
      rw [hg]
      exact hcountKeyTail
  have hcountLoad : Func.RunCompiled fs sevm
      (base.setMach ⟨countKey :: stack, M,
        G + 30 + countCost + temporalSloadCost sevm base countKey⟩)
      (Ninst.sload ::: pushB256 1 ::: add ::: newCountKey +++
        Ninst.sstore ::: .call finishSetPauserSlot) post := by
    exact Func.RunCompiled.next (temporal_sload_runCompiled hcount (by omega))
      hcountTail
  have hcountBody : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M,
        G + 42 + temporalSloadCost sevm base countKey + countCost⟩)
      (newCountKey +++ Ninst.sload ::: pushB256 1 ::: add :::
        newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot) post := by
    func_run (4) [3, countKey]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    all_goals try {
      simpa [countKey, countSlot, slot] using
        congrArg (fun x : B256 => (regionWord countRegion).or x) hnewValue }
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow]
    case a =>
      rw [hnewMemory]
      have hg : G + 42 + temporalSloadCost sevm base countKey +
          countCost - 12 =
          G + 30 + countCost + temporalSloadCost sevm base countKey := by
        omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (base.setMach ⟨countKey :: stack, M,
          G + 30 + countCost + temporalSloadCost sevm base countKey⟩)
        (Ninst.sload ::: pushB256 1 ::: add ::: newCountKey +++
          Ninst.sstore ::: .call finishSetPauserSlot) post
      exact hcountLoad
  have hbranch : Func.RunCompiled fs sevm
      (base.setMach ⟨0 :: stack, M,
        G + 55 + temporalSloadCost sevm base countKey + countCost⟩)
      ((.call removeTargetSlot) <?>
        (newCountKey +++ Ninst.sload ::: pushB256 1 ::: add :::
          newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot))
      post := by
    apply Func.RunCompiled.zero
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := base.setMach ⟨0 :: stack, M,
            G + 55 + temporalSloadCost sevm base countKey + countCost⟩)
          (x := (0 : B256)) (s := stack)
          (cost := gVerylow + gHigh)
          (G := G + 42 + temporalSloadCost sevm base countKey + countCost)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh]
            omega))
    · exact hcountBody
  simp only [afterOldPauser]
  func_run (3) [3]
  all_goals try ((try simp only [Devm.stack_setMach]); omega)
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hnewCovered]
    norm_num [gVerylow]
  case a =>
    rw [Mem.Reads.read hreads, hnew, hnewMemory]
    simp only [B256.eqCheck, if_neg hnewNonzero]
    have hg : G + 64 + temporalSloadCost sevm base countKey +
        countCost - 9 =
        G + 55 + temporalSloadCost sevm base countKey + countCost := by
      omega
    rw [hg]
    exact hbranch

def arrayLengthMemoryCost (M : Mem) : Nat :=
  calculateMemoryGasCost
      (memExtSize M.size (arrayLengthWord * 32).toNat 32) -
    calculateMemoryGasCost M.size

/-- State after the fresh path has read and replaced the target assignment. -/
def assignmentBase (sevm : Sevm) (base : Devm) (target : B256) : Devm :=
  temporalSloadBase sevm base (assignmentSlot target)

def assignmentPost (sevm : Sevm) (base : Devm)
    (target newPauser : B256) : Devm :=
  temporalSstorePost sevm (assignmentBase sevm base target)
    (assignmentSlot target) newPauser

theorem newPauserWord_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {value : B256} {stack : List B256} {G : Nat}
    {tail : Func} {post : Devm}
    (hvalue : (M.read (newPauserWord * 32).toNat 32).1.toB256 = value)
    (hmemory : (M.read (newPauserWord * 32).toNat 32).2 = M)
    (halign : M.size % 32 = 0)
    (hcovered : (newPauserWord * 32).toNat + 32 ≤ M.size)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨value :: stack, M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 6⟩)
      (loadWord newPauserWord +++ tail) post := by
  func_run (2) [3]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hcovered]
    norm_num [gVerylow]
  case a => rw [hvalue, hmemory]; exact htail
  all_goals first | omega | (simp only [Devm.stack_setMach]; omega)

theorem targetKey_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {target : B256} {stack : List B256} {G : Nat}
    {tail : Func} {post : Devm}
    (hvalue : (M.read (targetWord * 32).toNat 32).1.toB256 = target)
    (hmemory : (M.read (targetWord * 32).toNat 32).2 = M)
    (halign : M.size % 32 = 0)
    (hcovered : (targetWord * 32).toNat + 32 ≤ M.size)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨assignmentSlot target :: stack, M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 12⟩)
      (targetKey +++ tail) post := by
  func_run (4) [3, assignmentSlot target]
  all_goals try {
    simpa [assignmentSlot, slot] using
      congrArg (fun x : B256 =>
        (regionWord assignmentRegion).or x) hvalue }
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hcovered]
    norm_num [gVerylow]
  case a => rw [hmemory]; exact htail
  all_goals first | omega | (simp only [Devm.stack_setMach, List.length_cons]; omega)

theorem targetWord_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {value : B256} {stack : List B256} {G : Nat}
    {tail : Func} {post : Devm}
    (hvalue : (M.read (targetWord * 32).toNat 32).1.toB256 = value)
    (hmemory : (M.read (targetWord * 32).toNat 32).2 = M)
    (halign : M.size % 32 = 0)
    (hcovered : (targetWord * 32).toNat + 32 ≤ M.size)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨value :: stack, M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 6⟩)
      (loadWord targetWord +++ tail) post := by
  func_run (2) [3]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hcovered]
    norm_num [gVerylow]
  case a => rw [hvalue, hmemory]; exact htail
  all_goals first | omega | (simp only [Devm.stack_setMach]; omega)

theorem previousCountKey_prepend_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {M : Mem}
    {oldPauser : B256} {stack : List B256} {G : Nat}
    {tail : Func} {post : Devm}
    (hvalue : (M.read (previousPauserWord * 32).toNat 32).1.toB256 =
      oldPauser)
    (hmemory : (M.read (previousPauserWord * 32).toNat 32).2 = M)
    (halign : M.size % 32 = 0)
    (hcovered : (previousPauserWord * 32).toNat + 32 ≤ M.size)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨countSlot oldPauser :: stack, M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 12⟩)
      (previousCountKey +++ tail) post := by
  func_run (4) [3, countSlot oldPauser]
  all_goals try {
    simpa [countSlot, slot] using
      congrArg (fun x : B256 => (regionWord countRegion).or x) hvalue }
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hcovered]
    norm_num [gVerylow]
  case a => rw [hmemory]; exact htail
  all_goals first | omega |
    (simp only [Devm.stack_setMach, List.length_cons]; omega)

set_option maxRecDepth 16384 in
/-- Generic **old-last** arm of `registerAfterSet`: the previous pauser is
nonzero and its remaining assignment count is zero, so the walk clears that
pauser's heartbeat expiry to `0`, writes `0` into the event scratch word, and
emits `HeartbeatUpdated(oldPauser)` with a 32-byte zero payload before reaching
the shared new-pauser suffix, which is taken as a hypothesis.  Generic in that
suffix, so the same prefix serves the unregistration (`newPauser = 0`) and the
replacement (`newPauser ≠ 0`) chronologies.

Glue cost 1567 gas above the suffix, plus the expiry-clear `SSTORE` value cost:
22 for the outer previous-pauser load, `iszero` and untaken branch, 12 for
`previousCountKey`, 100 for the warm count `SLOAD`, 3 for its `iszero`, 14 for
the taken branch, then 14 for the zero value and the expiry key, 7 for the zero
event word and its `MSTORE`, and 1395 for the pauser load and the `LOG2`.

The count `SLOAD` is charged warm, which `hwarmCount` states as a premise
exactly as the retained-old sibling does; the Registry kernel has already read
and written that slot before control reaches here. -/
theorem registerAfterSet_oldLast_newPauserTail_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (oldPauser oldExpiry oldExpiryOriginal : B256)
    (stack : List B256) (clearCost G : Nat) (post : Devm)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
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
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (htail : Func.RunCompiled fs sevm
      (((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
          (0 : B256).toBytes⟩).setMach
        ⟨stack, M.write 0 (0 : B256).toBytes, G⟩)
      (loadWord newPauserWord +++ Ninst.iszero :::
        (Func.stop <?>
          (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++
            Ninst.sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 1567 + clearCost⟩)
      registerAfterSet post := by
  let newTail : Func :=
    loadWord newPauserWord +++ Ninst.iszero :::
      (Func.stop <?>
        (checkedHeartbeatExpiry <|
          dup 0 ::: mstoreAt 0 +++
          loadWord newPauserWord +++ tagTop expiryRegion +++
          Ninst.sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop))
  let clearPost := temporalSstorePost sevm base (expirySlot oldPauser) 0
  let M' := M.write 0 (0 : B256).toBytes
  let img' := Bytes.writeAt img 0 (0 : B256).toBytes
  have hzeroBytes : (0 : B256).toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes (0 : B256)
    rw [h] at hlen
    simp at hlen
  have hsizeM' : M'.size = M.size :=
    Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show 0 + 32 ≤ M.size by omega))
  have hsize' : 640 ≤ M'.size := by rw [hsizeM']; exact hsize
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads 0 _
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hpreviousCovered' :
      (previousPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']; exact hpreviousCovered
  have hzeroCovered' : 0 + 32 ≤ M'.size := by omega
  have hpreviousMemory :
      (M.read (previousPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hpreviousCovered)]
  have hpreviousMemory' :
      (M'.read (previousPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hpreviousCovered')]
  have hzeroMemory' : (M'.read 0 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hzeroCovered')]
  have hpreviousValue :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = oldPauser := by
    rw [Mem.Reads.read hreads]
    exact hprevious
  have hprevious' : Bytes.toB256
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      simp only [B256.length_toBytes]
      decide)]
    exact hprevious
  have hpreviousValue' :
      (M'.read (previousPauserWord * 32).toNat 32).1.toB256 = oldPauser := by
    rw [Mem.Reads.read hreads']
    exact hprevious'
  have hzeroRead' : (M'.read 0 32).1 = (0 : B256).toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M hzeroBytes)
  have hlogTail : Func.RunCompiled fs sevm
      (clearPost.setMach ⟨stack, M', G + 1395⟩)
      (loadWord previousPauserWord +++
        pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++ newTail) post := by
    func_run (6) [3, 1381]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign' hpreviousCovered']
      norm_num [gVerylow]
    case h_cost =>
      rw [hpreviousMemory']
      simp only [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((1 : B256) * 32).toNat = 32 by decide]
      rw [Devm.extCost_zero_of_le halign' hzeroCovered']
      norm_num [gLog, gLogdata, gLogtopic]
    case a =>
      rw [hpreviousMemory', hpreviousValue']
      simp only [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((1 : B256) * 32).toNat = 32 by decide]
      rw [hzeroRead', hzeroMemory']
      exact htail
  have hmstore : Func.RunCompiled fs sevm
      (clearPost.setMach ⟨stack, M, G + 1402⟩)
      (pushB256 0 ::: mstoreAt 0 +++ loadWord previousPauserWord +++
        pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++ newTail) post := by
    func_run (3) [0]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_ext =>
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_zero_of_le halign (by omega)]
    case a =>
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      exact hlogTail
  have hclear : Func.RunCompiled fs sevm
      (base.setMach ⟨expirySlot oldPauser :: (0 : B256) :: stack, M,
        G + 1402 + clearCost⟩)
      (Ninst.sstore ::: pushB256 0 ::: mstoreAt 0 +++
        loadWord previousPauserWord +++
        pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++ newTail) post :=
    Func.RunCompiled.next
      (temporal_sstore_runCompiled hexpiry hexpiryOrig hclearCost hwarmExpiry
        hgasStipend hstatic) hmstore
  have hkey : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 1416 + clearCost⟩)
      (pushB256 0 ::: loadWord previousPauserWord +++ tagTop expiryRegion +++
        Ninst.sstore ::: pushB256 0 ::: mstoreAt 0 +++
        loadWord previousPauserWord +++
        pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++ newTail) post := by
    have hor : (regionWord expiryRegion).or
        (M.read (previousPauserWord * 32).toNat 32).1.toB256 =
        expirySlot oldPauser := by
      simpa [expirySlot, slot] using
        congrArg (fun x : B256 => (regionWord expiryRegion).or x)
          hpreviousValue
    func_run (5) [3]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hpreviousCovered]
      norm_num [gVerylow]
    case a =>
      rw [hpreviousMemory, hor]
      have hg : G + 1416 + clearCost - 14 = G + 1402 + clearCost := by omega
      rw [hg]
      exact hclear
  have hcountTail : Func.RunCompiled fs sevm
      (base.setMach ⟨countSlot oldPauser :: stack, M, G + 1533 + clearCost⟩)
      (Ninst.sload ::: Ninst.iszero :::
        ((pushB256 0 ::: loadWord previousPauserWord +++
            tagTop expiryRegion +++ Ninst.sstore ::: pushB256 0 :::
            mstoreAt 0 +++ loadWord previousPauserWord +++
            pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++ newTail) <?>
          newTail)) post := by
    func_run (3) [1]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_val =>
      rw [Devm.getStorVal_setMach, hcount]
      simp [B256.eqCheck]
    case h_arm =>
      have hg : G + 1533 + clearCost - 117 = G + 1416 + clearCost := by omega
      rw [hg]
      exact hkey
  have holdTail : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 1545 + clearCost⟩)
      (previousCountKey +++ Ninst.sload ::: Ninst.iszero :::
        ((pushB256 0 ::: loadWord previousPauserWord +++
            tagTop expiryRegion +++ Ninst.sstore ::: pushB256 0 :::
            mstoreAt 0 +++ loadWord previousPauserWord +++
            pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++ newTail) <?>
          newTail)) post := by
    have hrun := previousCountKey_prepend_runCompiled hpreviousValue
      hpreviousMemory halign hpreviousCovered (by omega) hcountTail
    have hg : G + 1533 + clearCost + 12 = G + 1545 + clearCost := by omega
    rw [hg] at hrun
    exact hrun
  unfold registerAfterSet
  func_run (4) [3, 0]
  all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hpreviousCovered]
    norm_num [gVerylow]
  case h_val => simp [hpreviousValue, B256.eqCheck, holdNonzero]
  case h_arm =>
    rw [hpreviousMemory]
    have hg : G + 1567 + clearCost - 22 = G + 1545 + clearCost := by omega
    rw [hg]
    exact holdTail

set_option maxRecDepth 8192 in
/-- The checked expiry `SSTORE` and the `HeartbeatUpdated(newPauser)` record that
close every nonzero-new-pauser `registerAfterSet` arm, entered with the expiry
key and the computed expiry on the stack and the expiry already staged as the
event payload at memory offset `0`.

The stored value's `SSTORE` cost is caller-supplied, so nothing here assumes the
new pauser's expiry slot was previously zero. -/
private theorem registerAfterSet_expiryStoreLogTail_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (newPauser expiry currentExpiry expiryOriginal : B256)
    (stack : List B256) (storeCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hsize : 640 ≤ M.size)
    (halign : M.size % 32 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨expirySlot newPauser :: expiry :: stack,
        M.write 0 expiry.toBytes, G + 1395 + storeCost⟩)
      (Ninst.sstore :::
        loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
        logWith 1 0 1 +++ Func.stop)
      (((temporalSstorePost sevm base (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨stack, M.write 0 expiry.toBytes, G⟩) := by
  let M' := M.write 0 expiry.toBytes
  let storePost := temporalSstorePost sevm base (expirySlot newPauser) expiry
  have hsizeM' : M'.size = M.size := size_writeZero_word_of_le (by omega)
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have hnewCovered' : (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hzeroCovered' : 0 + 32 ≤ M'.size := by omega
  have hnewValue' :
      (M'.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [readNewPauser_after_writeZero hwf hreads, Mem.Reads.read hreads]
    exact hnew
  have hnewMemory' :
      (M'.read (newPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hnewCovered')]
  have hzeroMemory' : (M'.read 0 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hzeroCovered')]
  have hexpiryBytes : expiry.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes expiry
    rw [h] at hlen
    simp at hlen
  have hzeroRead' : (M'.read 0 32).1 = expiry.toBytes := by
    simpa only [B256.length_toBytes] using (Mem.read_write_zero M hexpiryBytes)
  have hsstore : Ninst.RunCompiled sevm
      (base.setMach ⟨expirySlot newPauser :: expiry :: stack, M',
        G + 1395 + storeCost⟩) Ninst.sstore
      (storePost.setMach ⟨stack, M', G + 1395⟩) :=
    temporal_sstore_runCompiled hexpiry hexpiryOrig hstoreCost hwarmExpiry
      hgasStipend hstatic
  have htail : Func.RunCompiled fs sevm
      (storePost.setMach ⟨stack, M', G + 1395⟩)
      (loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
        logWith 1 0 1 +++ Func.stop)
      ((storePost.addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach ⟨stack, M', G⟩) := by
    suffices h : ∃ out, Func.RunCompiled fs sevm
        (storePost.setMach ⟨stack, M', G + 1395⟩)
        (loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop) out ∧
        out = (storePost.addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
            expiry.toBytes⟩).setMach ⟨stack, M', G⟩ by
      obtain ⟨out, hrun, heq⟩ := h
      exact heq ▸ hrun
    apply Exists.intro
    constructor
    · func_run [3, 1381]
      all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
      case h_cost =>
        rw [Devm.extCost_zero_of_le halign' hnewCovered']
        norm_num [gVerylow]
      case h_cost =>
        rw [show ((0 : B256) * 32).toNat = 0 by decide,
          show ((1 : B256) * 32).toNat = 32 by decide]
        rw [hnewMemory']
        rw [Devm.extCost_zero_of_le halign' (by omega)]
        norm_num [gLog, gLogdata, gLogtopic]
      case a => exact Func.RunCompiled.last rfl
    · rw [hnewValue', hnewMemory']
      rw [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((1 : B256) * 32).toNat = 32 by decide]
      rw [hzeroRead', hzeroMemory']
      have hg : G + 1395 - 1395 = G := by omega
      rw [hg]
      rfl
  exact Func.RunCompiled.next hsstore htail

/-- Generic **nonzero-new-pauser** suffix of `registerAfterSet`: the shared
subterm all three arms reach after the previous pauser has been disposed of.  The
new-pauser scratch word is nonzero, so the walk computes the checked heartbeat
expiry from `block.timestamp` and the stored interval, stages it as the event
payload at memory offset `0`, stores it at the new pauser's expiry slot and emits
`HeartbeatUpdated(newPauser)`.

Glue cost 3569 gas above the caller's reserve, plus the expiry `SSTORE` value
cost: 22 for the new-pauser load, `iszero` and untaken branch, 2124 for
`checkedHeartbeatExpiry` (including the **cold** interval `SLOAD`, which
`hintervalCold` states as a premise), 14 for the untaken overflow branch, 14 for
the duplicated sum and its `MSTORE` at offset `0`, 12 for the expiry key, and
1395 for the store's own load-and-`LOG2` tail.

Generic in everything the branch does not fix.  In particular there is **no**
premise that the target was absent or that the previous pauser was zero — the
enclosing arm has already consumed that word — and the new pauser's current
expiry, its original value and the resulting `SSTORE` cost are all
caller-supplied, so a new pauser that already holds a live expiry instantiates
this as readily as a fresh one.  The memory bound is `640 ≤ M.size`, which the
found arm's 640 and the append arm's 704 both satisfy. -/
theorem registerAfterSet_nonzeroNewPauserTail_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (newPauser timestamp interval expiry currentExpiry expiryOriginal : B256)
    (stack : List B256) (storeCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hnewNonzero : newPauser ≠ 0)
    (hsize : 640 ≤ M.size)
    (halign : M.size % 32 = 0)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 3569 + storeCost⟩)
      (loadWord newPauserWord +++ Ninst.iszero :::
        (Func.stop <?>
          (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++
            Ninst.sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop)))
      (((temporalSstorePost sevm
          (temporalSloadBase sevm base heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨stack, M.write 0 expiry.toBytes, G⟩) := by
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewMemory : (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [Mem.Reads.read hreads]
    exact hnew
  have hsum := CheckedHeartbeatExtension.add_eq hextension
  have hle : timestamp ≤ expiry := by
    rcases hextension with ⟨bound, rfl⟩
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt bound]
    omega
  have hsizeM' : (M.write 0 expiry.toBytes).size = M.size :=
    size_writeZero_word_of_le (by omega)
  have halignM' : (M.write 0 expiry.toBytes).size % 32 = 0 := by
    rw [hsizeM']; exact halign
  have hnewCoveredM' :
      (newPauserWord * 32).toNat + 32 ≤ (M.write 0 expiry.toBytes).size := by
    rw [hsizeM']; exact hnewCovered
  have hnewValueM' :
      ((M.write 0 expiry.toBytes).read
        (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [readNewPauser_after_writeZero hwf hreads]
    exact hnewValue
  have hnewMemoryM' :
      ((M.write 0 expiry.toBytes).read
        (newPauserWord * 32).toNat 32).2 = M.write 0 expiry.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halignM' hnewCoveredM')]
  have hafterIntervalEq :
      temporalSloadBase sevm base heartbeatIntervalSlot =
        addAccessedStorageKey base sevm.currentTarget
          heartbeatIntervalSlot := by
    simp only [temporalSloadBase, if_neg hintervalCold]
  have htail := registerAfterSet_expiryStoreLogTail_runCompiled fs sevm
    (temporalSloadBase sevm base heartbeatIntervalSlot) M img newPauser expiry
    currentExpiry expiryOriginal stack storeCost G hstack hwf hreads hnew hsize
    halign (by rw [temporalSloadBase_getStorVal]; exact hexpiry) hexpiryOrig
    (temporalSloadBase_preserves_warm sevm base heartbeatIntervalSlot
      (expirySlot newPauser) hwarmExpiry)
    hstoreCost hgasStipend hstatic
  func_run (20) [3, 0, expiry, 0, 0, 3, expirySlot newPauser]
  all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hnewCovered]
    norm_num [gVerylow]
  case h_val =>
    rw [hnewValue]
    simp [B256.eqCheck, hnewNonzero]
  case h_val =>
    simp only [Devm.getStorVal_setMach]
    rw [hinterval, htime, B256.add_comm, hsum]
  case h_val =>
    rw [htime]
    simp [B256.ltCheck, hle]
  case h_ext =>
    rw [hnewMemory]
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    rw [Devm.extCost_zero_of_le halign (by omega)]
  case h_cost =>
    rw [hnewMemory]
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    rw [Devm.extCost_zero_of_le halignM' hnewCoveredM']
    norm_num [gVerylow]
  case h_val =>
    rw [hnewMemory]
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    rw [hnewValueM']
    rfl
  case a =>
    rw [addAccessedStorageKey_setMach_setMach, hnewMemory]
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    rw [hnewMemoryM', ← hafterIntervalEq]
    have hg : G + 3569 + storeCost - 2174 = G + 1395 + storeCost := by omega
    rw [hg]
    exact htail

/-- Exact kernel prefix reserve for the append arm: the outer nonzero guard
and the assignment replacement for a target whose recorded pauser is zero,
measured above whatever the `appendTarget` continuation itself consumes. -/
def appendSetPauserKernelPrefixGas (sevm : Sevm) (base : Devm)
    (target : B256) (assignmentCost : Nat) : Nat :=
  90 + temporalSloadCost sevm base (assignmentSlot target) + assignmentCost

/-- Generated-kernel walk for a target whose recorded pauser is zero: the
outer nonzero guard passes, the zero previous pauser is saved to memory, the
assignment is overwritten with `newPauser`, and the `iszero` branch selects
`appendTarget`, taken as a hypothesis from the assignment-updated state at
`Ga` gas.  Generic in `newPauser`, so it serves both the fresh and the
absent-zero chronologies. -/
theorem setPauserKernel_append_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (out : Devm)
    (target newPauser : B256) (assignmentOriginal : B256)
    (assignmentCost Ga : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (htargetValid : nonzeroCanonicalAddress target)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hassignment : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = 0)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 newPauser =
      assignmentCost)
    (hgasStore : gCallStipend < Ga + 29 + assignmentCost)
    (hstatic : sevm.isStatic = false)
    (happend :
      let M' := M.write (previousPauserWord * 32).toNat (0 : B256).toBytes
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        ((assignmentPost sevm base target newPauser).setMach
          ⟨[], M', Ga⟩)
        appendTarget out) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M,
        Ga + appendSetPauserKernelPrefixGas sevm base target
          assignmentCost⟩)
      setPauserKernel out := by
  dsimp only at happend
  let fs := (runtime dp).main :: (runtime dp).aux
  let assignmentKey := assignmentSlot target
  let assignBase := assignmentBase sevm base target
  let assignPost := assignmentPost sevm base target newPauser
  let M' := M.write (previousPauserWord * 32).toNat (0 : B256).toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  have hassignmentBase : assignBase.getStorVal sevm.currentTarget
      assignmentKey = 0 := by
    simpa only [assignBase, assignmentBase,
      temporalSloadBase_getStorVal] using hassignment
  have hwarmAssignment : (sevm.currentTarget, assignmentKey) ∈
      assignBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm base assignmentKey
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by
            decide
          omega))
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have htarget' : Bytes.toB256
      (img'.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have htargetCovered' : (targetWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    exact htargetCovered
  have hnewCovered' : (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have htargetMemory : (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have htargetMemory' : (M'.read (targetWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' htargetCovered')]
  have hnewMemory' : (M'.read (newPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hnewCovered')]
  have htargetValue : (M.read (targetWord * 32).toNat 32).1.toB256 =
      target := by rw [Mem.Reads.read hreads]; exact htarget
  have htargetValue' : (M'.read (targetWord * 32).toNat 32).1.toB256 =
      target := by rw [Mem.Reads.read hreads']; exact htarget'
  have hnewValue' : (M'.read (newPauserWord * 32).toNat 32).1.toB256 =
      newPauser := by rw [Mem.Reads.read hreads']; exact hnew'
  have happendLookup : fs[appendTargetSlot]? = some appendTarget := by
    simp [fs, runtime, aux, appendTargetSlot]
  have happendCall : Func.RunCompiled fs sevm
      (assignPost.setMach ⟨[], M', Ga + 12⟩)
      (.call appendTargetSlot) out := by
    apply Func.RunCompiled.call happendLookup (by
      simp only [Devm.stack_setMach, List.length_nil]
      decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := assignPost.setMach ⟨[], M', Ga + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := Ga)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact happend
  have hbranch : Func.RunCompiled fs sevm
      (assignPost.setMach ⟨[1], M', Ga + 26⟩)
      ((.call appendTargetSlot) <?>
        (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot))
      out := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide) (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := assignPost.setMach ⟨[1], M', Ga + 26⟩)
          (x := (1 : B256)) (s := [])
          (cost := gVerylow + gHigh + gJumpdest) (G := Ga + 12)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]))
    · exact happendCall
  have hiszero : Func.RunCompiled fs sevm
      (assignPost.setMach ⟨[0], M', Ga + 29⟩)
      (Ninst.iszero ::: ((.call appendTargetSlot) <?>
        (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    func_run (1) [1]
    case a => exact hbranch
  have hstore : Func.RunCompiled fs sevm
      (assignBase.setMach
        ⟨[assignmentKey, newPauser, 0], M', Ga + 29 + assignmentCost⟩)
      (Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hassignmentBase hassignmentOrig
        hassignmentCost hwarmAssignment hgasStore hstatic)
      hiszero
  have htargetKeySecond : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[newPauser, 0], M',
        Ga + 41 + assignmentCost⟩)
      (targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    simp only [assignmentKey] at hstore
    have hrun := targetKey_prepend_runCompiled htargetValue' htargetMemory'
      halign' htargetCovered' (by simp) hstore
    have hg : Ga + 29 + assignmentCost + 12 =
        Ga + 41 + assignmentCost := by omega
    rw [hg] at hrun
    exact hrun
  have hnewTail : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[0], M', Ga + 47 + assignmentCost⟩)
      (loadWord newPauserWord +++ targetKey +++ Ninst.sstore :::
        Ninst.iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    have hrun := newPauserWord_prepend_runCompiled hnewValue' hnewMemory'
      halign' hnewCovered' (by simp) htargetKeySecond
    have hg : Ga + 41 + assignmentCost + 6 =
        Ga + 47 + assignmentCost := by omega
    rw [hg] at hrun
    exact hrun
  have hsavePrevious : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[0, 0], M,
        Ga + 53 + assignmentCost⟩)
      (mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    func_run (2) [0]
    case h_ext =>
      rw [Devm.extCost_zero_of_le halign (by
        have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
        omega)]
    case a =>
      have hg : Ga + 53 + assignmentCost - 6 =
          Ga + 47 + assignmentCost := by omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (assignBase.setMach ⟨[0], M', Ga + 47 + assignmentCost⟩)
        _ out
      exact hnewTail
  have hdup : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[0], M, Ga + 56 + assignmentCost⟩)
      (dup 0 ::: mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    func_run (1)
    case a =>
      have hg : Ga + 56 + assignmentCost - 3 =
          Ga + 53 + assignmentCost := by omega
      rw [hg]
      exact hsavePrevious
  have hsload : Func.RunCompiled fs sevm
      (base.setMach ⟨[assignmentKey], M,
        Ga + 56 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      (Ninst.sload ::: dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ Ninst.sstore :::
        Ninst.iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    exact Func.RunCompiled.next
      (temporal_sload_runCompiled hassignment (by decide)) hdup
  have htargetKeyFirst : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M,
        Ga + 68 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      (targetKey +++ Ninst.sload ::: dup 0 :::
        mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    simp only [assignmentKey] at hsload
    have hrun := targetKey_prepend_runCompiled htargetValue htargetMemory
      halign htargetCovered (by simp) hsload
    have hg : Ga + 56 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) + 12 =
        Ga + 68 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) := by omega
    rw [hg] at hrun
    exact hrun
  have hguardBranch : Func.RunCompiled fs sevm
      (base.setMach ⟨[0], M,
        Ga + 81 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ Ninst.sload ::: dup 0 :::
          mstoreAt previousPauserWord +++ loadWord newPauserWord +++
          targetKey +++ Ninst.sstore ::: Ninst.iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
              sub ::: previousCountKey +++ Ninst.sstore :::
              .call afterOldPauserSlot))))
      out := by
    apply Func.RunCompiled.zero (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    · have hg : Ga + 81 + assignmentCost +
          temporalSloadCost sevm base assignmentKey =
          Ga + 68 + assignmentCost +
            temporalSloadCost sevm base assignmentKey + 13 := by omega
      rw [hg]
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using (Devm.popBurnBy_setMach
          (devm := base.setMach ⟨[0], M,
            Ga + 68 + assignmentCost +
              temporalSloadCost sevm base assignmentKey + 13⟩)
          (x := (0 : B256)) (s := []) (cost := gVerylow + gHigh)
          (G := Ga + 68 + assignmentCost +
            temporalSloadCost sevm base assignmentKey)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh]))
    · exact htargetKeyFirst
  have hguard : Func.RunCompiled fs sevm
      (base.setMach ⟨[target], M,
        Ga + 84 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      (Ninst.iszero ::: ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ Ninst.sload ::: dup 0 :::
          mstoreAt previousPauserWord +++ loadWord newPauserWord +++
          targetKey +++ Ninst.sstore ::: Ninst.iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
              sub ::: previousCountKey +++ Ninst.sstore :::
              .call afterOldPauserSlot)))))
      out := by
    func_run (1) [0]
    case h_val =>
      change (if target = 0 then (1 : B256) else 0) = 0
      rw [if_neg htargetValid.1]
    case a =>
      have hg : Ga + 84 + assignmentCost +
            temporalSloadCost sevm base assignmentKey - 3 =
          Ga + 81 + assignmentCost +
            temporalSloadCost sevm base assignmentKey := by omega
      rw [hg]
      exact hguardBranch
  have hkernel : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M,
        Ga + 90 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      setPauserKernel out := by
    have hrun := targetWord_prepend_runCompiled htargetValue htargetMemory
      halign htargetCovered (by simp) hguard
    have hg : Ga + 84 + assignmentCost +
          temporalSloadCost sevm base assignmentKey + 6 =
        Ga + 90 + assignmentCost +
          temporalSloadCost sevm base assignmentKey := by omega
    rw [hg] at hrun
    simpa only [setPauserKernel] using hrun
  have hg : Ga + appendSetPauserKernelPrefixGas sevm base target
        assignmentCost =
      Ga + 90 + assignmentCost +
        temporalSloadCost sevm base assignmentKey := by
    dsimp only [appendSetPauserKernelPrefixGas, assignmentKey]
    omega
  rw [hg]
  simpa only [fs] using hkernel

/-- Exact kernel prefix reserve for the found-target arm: the outer nonzero
guard, the assignment replacement, and the old-count decrement, measured above
whatever the `afterOldPauser` continuation itself consumes. -/
def foundSetPauserKernelPrefixGas (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser : B256)
    (assignmentCost countCost : Nat) : Nat :=
  122 + temporalSloadCost sevm base (assignmentSlot target) + assignmentCost +
    temporalSloadCost sevm (assignmentPost sevm base target newPauser)
      (countSlot oldPauser) + countCost

/-- Generated-kernel walk for a target whose recorded pauser is nonzero: the
assignment is overwritten with `newPauser`, the old pauser is saved to memory,
and its assignment count is decremented before control reaches
`afterOldPauser`.  Generic in `newPauser`, so it serves both unregistration
(`newPauser = 0`) and replacement.  The memory premise is a lower bound and
word alignment rather than the register image's exact `640`: every window this
walk touches sits below `640`, so any aligned image at least that large serves
— a larger staged image included. -/
theorem setPauserKernel_found_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (out : Devm)
    (target newPauser oldPauser oldCount : B256)
    (assignmentOriginal countOriginal : B256)
    (assignmentCost countCost afterGas G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hsizeLow : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hassignment : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser
      newPauser = assignmentCost)
    (hcount : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hgasFinal : gCallStipend < G + afterGas + 12 + countCost)
    (hstatic : sevm.isStatic = false)
    (hafter :
      let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
      let countBase := temporalSloadBase sevm
        (assignmentPost sevm base target newPauser)
        (countSlot oldPauser)
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        ((temporalSstorePost sevm countBase (countSlot oldPauser)
          (oldCount - 1)).setMach ⟨[], M', G + afterGas⟩)
        afterOldPauser out) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M,
        G + afterGas + foundSetPauserKernelPrefixGas sevm base target
          newPauser oldPauser assignmentCost countCost⟩)
      setPauserKernel out := by
  dsimp only at hafter
  let fs := (runtime dp).main :: (runtime dp).aux
  let assignBase := assignmentBase sevm base target
  let assignPost := assignmentPost sevm base target newPauser
  let countBase := temporalSloadBase sevm assignPost (countSlot oldPauser)
  let countPost := temporalSstorePost sevm countBase (countSlot oldPauser)
    (oldCount - 1)
  let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    oldPauser.toBytes
  let elseGas := G + afterGas + 45 + countCost +
    temporalSloadCost sevm assignPost (countSlot oldPauser)
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hpreviousCovered : (previousPauserWord * 32).toNat + 32 ≤ M.size :=
    Nat.le_trans (show (previousPauserWord * 32).toNat + 32 ≤ 640 by decide)
      hsizeLow
  have hsizeM' : M'.size = M.size :=
    Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using hpreviousCovered)
  have hsizeLow' : 640 ≤ M'.size := by rw [hsizeM']; exact hsizeLow
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have htarget' : Bytes.toB256
      (img'.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hprevious' : Bytes.toB256
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser := by
    dsimp only [img']
    rw [show 32 = oldPauser.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size :=
    Nat.le_trans (show (targetWord * 32).toNat + 32 ≤ 640 by decide) hsizeLow
  have htargetCovered' : (targetWord * 32).toNat + 32 ≤ M'.size :=
    Nat.le_trans (show (targetWord * 32).toNat + 32 ≤ 640 by decide) hsizeLow'
  have hnewCovered' : (newPauserWord * 32).toNat + 32 ≤ M'.size :=
    Nat.le_trans (show (newPauserWord * 32).toNat + 32 ≤ 640 by decide)
      hsizeLow'
  have hpreviousCovered' :
      (previousPauserWord * 32).toNat + 32 ≤ M'.size :=
    Nat.le_trans (show (previousPauserWord * 32).toNat + 32 ≤ 640 by decide)
      hsizeLow'
  have htargetMemory : (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have htargetMemory' : (M'.read (targetWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' htargetCovered')]
  have hnewMemory' : (M'.read (newPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hnewCovered')]
  have hpreviousMemory' :
      (M'.read (previousPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hpreviousCovered')]
  have htargetValue : (M.read (targetWord * 32).toNat 32).1.toB256 =
      target := by rw [Mem.Reads.read hreads]; exact htarget
  have htargetValue' : (M'.read (targetWord * 32).toNat 32).1.toB256 =
      target := by rw [Mem.Reads.read hreads']; exact htarget'
  have hnewValue' : (M'.read (newPauserWord * 32).toNat 32).1.toB256 =
      newPauser := by rw [Mem.Reads.read hreads']; exact hnew'
  have hpreviousValue' :
      (M'.read (previousPauserWord * 32).toNat 32).1.toB256 = oldPauser := by
    rw [Mem.Reads.read hreads']; exact hprevious'
  have hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser := by
    simp [fs, runtime, aux, afterOldPauserSlot]
  have hafterCall : Func.RunCompiled fs sevm
      (countPost.setMach ⟨[], M', G + afterGas + 12⟩)
      (.call afterOldPauserSlot) out := by
    apply Func.RunCompiled.call hafterLookup (by
      simp only [Devm.stack_setMach, List.length_nil]
      decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := countPost.setMach ⟨[], M', G + afterGas + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G + afterGas)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hafter
  have hcountBase : countBase.getStorVal sevm.currentTarget
      (countSlot oldPauser) = oldCount := by
    simpa only [countBase, temporalSloadBase_getStorVal] using hcount
  have hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      countBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm assignPost (countSlot oldPauser)
  have hstoreCount : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[countSlot oldPauser, oldCount - 1], M',
        G + afterGas + 12 + countCost⟩)
      (Ninst.sstore ::: .call afterOldPauserSlot) out :=
    Func.RunCompiled.next
      (temporal_sstore_runCompiled hcountBase hcountOrig hcountCost hwarmCount
        hgasFinal hstatic) hafterCall
  have hcountKeyStore : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[oldCount - 1], M',
        G + afterGas + 24 + countCost⟩)
      (previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)
      out := by
    have hrun := previousCountKey_prepend_runCompiled hpreviousValue'
      hpreviousMemory' halign' hpreviousCovered' (by simp) hstoreCount
    have hg : G + afterGas + 12 + countCost + 12 =
        G + afterGas + 24 + countCost := by omega
    rw [hg] at hrun
    exact hrun
  have harith : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[oldCount], M', G + afterGas + 33 + countCost⟩)
      (pushB256 1 ::: swap 0 ::: sub ::: previousCountKey +++ Ninst.sstore :::
        .call afterOldPauserSlot) out := by
    func_run (3)
    case a =>
      have hg : G + afterGas + 33 + countCost - 9 =
          G + afterGas + 24 + countCost := by omega
      rw [hg]
      exact hcountKeyStore
  have hcountSload : Func.RunCompiled fs sevm
      (assignPost.setMach ⟨[countSlot oldPauser], M',
        G + afterGas + 33 + countCost +
          temporalSloadCost sevm assignPost (countSlot oldPauser)⟩)
      (Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
        previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)
      out :=
    Func.RunCompiled.next (temporal_sload_runCompiled hcount (by decide))
      harith
  have helse : Func.RunCompiled fs sevm
      (assignPost.setMach ⟨[], M', elseGas⟩)
      (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
        previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)
      out := by
    have hrun := previousCountKey_prepend_runCompiled hpreviousValue'
      hpreviousMemory' halign' hpreviousCovered' (by simp) hcountSload
    have hg : G + afterGas + 33 + countCost +
          temporalSloadCost sevm assignPost (countSlot oldPauser) + 12 =
        elseGas := by
      dsimp only [elseGas]
      omega
    rw [hg] at hrun
    exact hrun
  have hbranch : Func.RunCompiled fs sevm
      (assignPost.setMach ⟨[0], M', elseGas + 13⟩)
      ((.call appendTargetSlot) <?>
        (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot))
      out := by
    apply Func.RunCompiled.zero (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := assignPost.setMach ⟨[0], M', elseGas + 13⟩)
          (x := (0 : B256)) (s := []) (cost := gVerylow + gHigh)
          (G := elseGas)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh]))
    · exact helse
  have hiszero : Func.RunCompiled fs sevm
      (assignPost.setMach ⟨[oldPauser], M', elseGas + 16⟩)
      (Ninst.iszero ::: ((.call appendTargetSlot) <?>
        (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      out := by
    func_run (1) [0]
    case h_val =>
      change (if oldPauser = 0 then (1 : B256) else 0) = 0
      rw [if_neg holdValid.1]
    case a =>
      have hg : elseGas + 16 - 3 = elseGas + 13 := by omega
      rw [hg]
      exact hbranch
  have hassignmentBase : assignBase.getStorVal sevm.currentTarget
      (assignmentSlot target) = oldPauser := by
    simpa only [assignBase, assignmentBase,
      temporalSloadBase_getStorVal] using hassignment
  have hwarmAssignment : (sevm.currentTarget, assignmentSlot target) ∈
      assignBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm base (assignmentSlot target)
  have hstore : Func.RunCompiled fs sevm
      (assignBase.setMach
        ⟨[assignmentSlot target, newPauser, oldPauser], M',
          elseGas + 16 + assignmentCost⟩)
      (Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
            sub ::: previousCountKey +++ Ninst.sstore :::
            .call afterOldPauserSlot)))
      out := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hassignmentBase hassignmentOrig
        hassignmentCost hwarmAssignment (by
          dsimp only [elseGas]
          omega) hstatic)
      hiszero
  have htargetKeySecond : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[newPauser, oldPauser], M',
        elseGas + 28 + assignmentCost⟩)
      (targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
            sub ::: previousCountKey +++ Ninst.sstore :::
            .call afterOldPauserSlot)))
      out := by
    have hrun := targetKey_prepend_runCompiled htargetValue' htargetMemory'
      halign' htargetCovered' (by simp) hstore
    have hg : elseGas + 16 + assignmentCost + 12 =
        elseGas + 28 + assignmentCost := by omega
    rw [hg] at hrun
    exact hrun
  have hnewTail : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[oldPauser], M',
        elseGas + 34 + assignmentCost⟩)
      (loadWord newPauserWord +++ targetKey +++ Ninst.sstore :::
        Ninst.iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
            sub ::: previousCountKey +++ Ninst.sstore :::
            .call afterOldPauserSlot)))
      out := by
    have hrun := newPauserWord_prepend_runCompiled hnewValue' hnewMemory'
      halign' hnewCovered' (by simp) htargetKeySecond
    have hg : elseGas + 28 + assignmentCost + 6 =
        elseGas + 34 + assignmentCost := by omega
    rw [hg] at hrun
    exact hrun
  have hsavePrevious : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[oldPauser, oldPauser], M,
        elseGas + 40 + assignmentCost⟩)
      (mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
            sub ::: previousCountKey +++ Ninst.sstore :::
            .call afterOldPauserSlot)))
      out := by
    func_run (2) [0]
    case h_ext =>
      rw [Devm.extCost_zero_of_le halign (Nat.le_trans (by decide) hsizeLow)]
    case a =>
      have hg : elseGas + 40 + assignmentCost - 6 =
          elseGas + 34 + assignmentCost := by omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (assignBase.setMach ⟨[oldPauser], M',
          elseGas + 34 + assignmentCost⟩) _ out
      exact hnewTail
  have hdup : Func.RunCompiled fs sevm
      (assignBase.setMach ⟨[oldPauser], M,
        elseGas + 43 + assignmentCost⟩)
      (dup 0 ::: mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
            sub ::: previousCountKey +++ Ninst.sstore :::
            .call afterOldPauserSlot)))
      out := by
    func_run (1)
    case a =>
      have hg : elseGas + 43 + assignmentCost - 3 =
          elseGas + 40 + assignmentCost := by omega
      rw [hg]
      exact hsavePrevious
  have hsload : Func.RunCompiled fs sevm
      (base.setMach ⟨[assignmentSlot target], M,
        elseGas + 43 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target)⟩)
      (Ninst.sload ::: dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ Ninst.sstore :::
        Ninst.iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
            sub ::: previousCountKey +++ Ninst.sstore :::
            .call afterOldPauserSlot)))
      out :=
    Func.RunCompiled.next (temporal_sload_runCompiled hassignment (by decide))
      hdup
  have htargetKeyFirst : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M,
        elseGas + 55 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target)⟩)
      (targetKey +++ Ninst.sload ::: dup 0 :::
        mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
            sub ::: previousCountKey +++ Ninst.sstore :::
            .call afterOldPauserSlot)))
      out := by
    have hrun := targetKey_prepend_runCompiled htargetValue htargetMemory
      halign htargetCovered (by simp) hsload
    have hg : elseGas + 43 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) + 12 =
        elseGas + 55 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) := by omega
    rw [hg] at hrun
    exact hrun
  have hguardBranch : Func.RunCompiled fs sevm
      (base.setMach ⟨[0], M,
        elseGas + 68 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target)⟩)
      ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ Ninst.sload ::: dup 0 :::
          mstoreAt previousPauserWord +++ loadWord newPauserWord +++
          targetKey +++ Ninst.sstore ::: Ninst.iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
              sub ::: previousCountKey +++ Ninst.sstore :::
              .call afterOldPauserSlot))))
      out := by
    apply Func.RunCompiled.zero (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    · have hg : elseGas + 68 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) =
          elseGas + 55 + assignmentCost +
            temporalSloadCost sevm base (assignmentSlot target) + 13 := by
        omega
      rw [hg]
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using (Devm.popBurnBy_setMach
          (devm := base.setMach ⟨[0], M,
            elseGas + 55 + assignmentCost +
              temporalSloadCost sevm base (assignmentSlot target) + 13⟩)
          (x := (0 : B256)) (s := []) (cost := gVerylow + gHigh)
          (G := elseGas + 55 + assignmentCost +
            temporalSloadCost sevm base (assignmentSlot target))
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh]))
    · exact htargetKeyFirst
  have hguard : Func.RunCompiled fs sevm
      (base.setMach ⟨[target], M,
        elseGas + 71 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target)⟩)
      (Ninst.iszero ::: ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ Ninst.sload ::: dup 0 :::
          mstoreAt previousPauserWord +++ loadWord newPauserWord +++
          targetKey +++ Ninst.sstore ::: Ninst.iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 :::
              sub ::: previousCountKey +++ Ninst.sstore :::
              .call afterOldPauserSlot)))))
      out := by
    func_run (1) [0]
    case h_val =>
      change (if target = 0 then (1 : B256) else 0) = 0
      rw [if_neg htargetValid.1]
    case a =>
      have hg : elseGas + 71 + assignmentCost +
            temporalSloadCost sevm base (assignmentSlot target) - 3 =
          elseGas + 68 + assignmentCost +
            temporalSloadCost sevm base (assignmentSlot target) := by omega
      rw [hg]
      exact hguardBranch
  have hkernel : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M,
        elseGas + 77 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target)⟩)
      setPauserKernel out := by
    have hrun := targetWord_prepend_runCompiled htargetValue htargetMemory
      halign htargetCovered (by simp) hguard
    have hg : elseGas + 71 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) + 6 =
        elseGas + 77 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) := by omega
    rw [hg] at hrun
    simpa only [setPauserKernel] using hrun
  have hg : G + afterGas + foundSetPauserKernelPrefixGas sevm base target
        newPauser oldPauser assignmentCost countCost =
      elseGas + 77 + assignmentCost +
        temporalSloadCost sevm base (assignmentSlot target) := by
    dsimp only [foundSetPauserKernelPrefixGas, elseGas, assignPost]
    omega
  rw [hg]
  simpa only [fs] using hkernel

/-- State reached by the found-target kernel prefix: the target's assignment has
been replaced by `newPauser` and the old pauser's count has been decremented.
This is a four-layer `temporalSstorePost`/`temporalSloadBase` tower; keep it
folded under this name and never cross it by `exact`, `change` or `rfl`.  See
README.md, *Proof-performance conventions*. -/
def foundKernelPost (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount : B256) : Devm :=
  temporalSstorePost sevm
    (temporalSloadBase sevm (assignmentPost sevm base target newPauser)
      (countSlot oldPauser))
    (countSlot oldPauser) (oldCount - 1)

/-- Complete Registry walk for the found-target arm with a **nonzero** new
pauser — the replacement chronology's three writes.  The kernel prefix replaces
the assignment and decrements the old pauser's count, then `afterOldPauser`
takes its nonzero arm and stores `count[new] + 1`, reaching `finishSetPauser`,
which is taken as a hypothesis.

Generic in both pausers and in every stored value, so the distinct, same-pauser
and already-owning replacement partitions all instantiate it.  The new count is
read from `foundKernelPost` — the poststate of the old-count decrement — so no
disjointness between the two count slots is assumed, which is exactly what the
same-pauser partition needs. -/
theorem setPauserKernel_foundNonzero_finishSetPauser_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (out : Devm)
    (target newPauser oldPauser oldCount newCount nextCount : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (htargetValid : nonzeroCanonicalAddress target)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hnewNonzero : newPauser ≠ 0)
    (hsize : M.size = 640)
    (hassignment : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = oldPauser)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser
      newPauser = assignmentCost)
    (hcount : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hnewCount :
      (foundKernelPost sevm base target newPauser oldPauser
        oldCount).getStorVal sevm.currentTarget (countSlot newPauser) =
        newCount)
    (hnewCountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot newPauser) = newCountOriginal)
    (hnewCountNext : (1 : B256) + newCount = nextCount)
    (hnewCountCost : sstoreValueCost newCountOriginal newCount nextCount =
      newCountCost)
    (hgasStipend : gCallStipend < G + 12 + newCountCost)
    (hstatic : sevm.isStatic = false)
    (hfinish :
      let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
      let countPost := foundKernelPost sevm base target newPauser oldPauser
        oldCount
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        ((temporalSstorePost sevm
          (temporalSloadBase sevm countPost (countSlot newPauser))
          (countSlot newPauser) nextCount).setMach ⟨[], M', G⟩)
        finishSetPauser out) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M,
        G + (64 + temporalSloadCost sevm
            (foundKernelPost sevm base target newPauser oldPauser oldCount)
            (countSlot newPauser) + newCountCost) +
          foundSetPauserKernelPrefixGas sevm base target newPauser oldPauser
            assignmentCost countCost⟩)
      setPauserKernel out := by
  dsimp only at hfinish
  let M' := M.write (previousPauserWord * 32).toNat oldPauser.toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    oldPauser.toBytes
  have halign : M.size % 32 = 0 := by rw [hsize]
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsize' : M'.size = 640 := by
    rw [Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          rw [hsize]
          decide))]
    exact hsize
  have halign' : M'.size % 32 = 0 := by rw [hsize']
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp only [img']
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hafter := afterOldPauser_finishSetPauser_runCompiled dp sevm
    (foundKernelPost sevm base target newPauser oldPauser oldCount) M' img'
    newPauser newCount nextCount newCountOriginal [] newCountCost G out
    (by simp) hreads' hnew' hnewNonzero (by omega) halign' hnewCount
    hnewCountOrig hnewCountNext hnewCountCost hgasStipend hstatic hfinish
  have hg : G + 64 + temporalSloadCost sevm
        (foundKernelPost sevm base target newPauser oldPauser oldCount)
        (countSlot newPauser) + newCountCost =
      G + (64 + temporalSloadCost sevm
        (foundKernelPost sevm base target newPauser oldPauser oldCount)
        (countSlot newPauser) + newCountCost) := by omega
  rw [hg] at hafter
  exact setPauserKernel_found_runCompiled dp sevm base M img out target
    newPauser oldPauser oldCount assignmentOriginal countOriginal
    assignmentCost countCost
    (64 + temporalSloadCost sevm
      (foundKernelPost sevm base target newPauser oldPauser oldCount)
      (countSlot newPauser) + newCountCost) G
    hwf hreads htarget hnew htargetValid holdValid hsize.symm.le halign
    hassignment hassignmentOrig hassignmentCost hcount hcountOrig hcountCost
    (by omega) hstatic hafter

/-! ## Fresh registration public boundary -/

def registerMemory (target newPauser : B256) : Mem :=
  (((Mem.empty.write (targetWord * 32).toNat target.toBytes).write
      (newPauserWord * 32).toNat newPauser.toBytes).write
      (previousPauserWord * 32).toNat (0 : B256).toBytes).write
      (continuationWord * 32).toNat (0 : B256).toBytes

def registerImage (target newPauser : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt [] (targetWord * 32).toNat target.toBytes)
        (newPauserWord * 32).toNat newPauser.toBytes)
      (previousPauserWord * 32).toNat (0 : B256).toBytes)
    (continuationWord * 32).toNat (0 : B256).toBytes

theorem registerMemory_spec (target newPauser : B256) :
    let M := registerMemory target newPauser
    let img := registerImage target newPauser
    Mem.Wf M ∧ Mem.Reads M img ∧ M.size = 640 ∧
      Bytes.toB256 (img.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Bytes.toB256 (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser ∧
      Bytes.toB256 (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0 ∧
      Bytes.toB256 (img.sliceD (continuationWord * 32).toNat 32 0) = 0 := by
  let M0 := Mem.empty
  let img0 : Bytes := []
  let M1 := M0.write (targetWord * 32).toNat target.toBytes
  let img1 := Bytes.writeAt img0 (targetWord * 32).toNat target.toBytes
  let M2 := M1.write (newPauserWord * 32).toNat newPauser.toBytes
  let img2 := Bytes.writeAt img1 (newPauserWord * 32).toNat newPauser.toBytes
  let M3 := M2.write (previousPauserWord * 32).toNat (0 : B256).toBytes
  let img3 := Bytes.writeAt img2 (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  let M4 := M3.write (continuationWord * 32).toNat (0 : B256).toBytes
  let img4 := Bytes.writeAt img3 (continuationWord * 32).toNat
    (0 : B256).toBytes
  have hwf0 : Mem.Wf M0 := Mem.wf_empty
  have hreads0 : Mem.Reads M0 img0 := Mem.reads_empty
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  have hreads1 : Mem.Reads M1 img1 := Mem.Reads.write hwf0 hreads0 _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hreads2 : Mem.Reads M2 img2 := Mem.Reads.write hwf1 hreads1 _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hreads3 : Mem.Reads M3 img3 := Mem.Reads.write hwf2 hreads2 _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hreads4 : Mem.Reads M4 img4 := Mem.Reads.write hwf3 hreads3 _ _
  have hsize1 : M1.size = 544 := by
    dsimp only [M1, M0]
    rw [Mem.size_write_word_at]
    decide +kernel
  have hsize2 : M2.size = 576 := by
    dsimp only [M2]
    rw [Mem.size_write_word_at, hsize1]
    decide +kernel
  have hsize3 : M3.size = 608 := by
    dsimp only [M3]
    rw [Mem.size_write_word_at, hsize2]
    decide +kernel
  have hsize4 : M4.size = 640 := by
    dsimp only [M4]
    rw [Mem.size_write_word_at, hsize3]
    decide +kernel
  have sliceAt (bs : Bytes) (word value : B256) :
      Bytes.toB256
          ((Bytes.writeAt bs (word * 32).toNat value.toBytes).sliceD
            (word * 32).toNat 32 0) = value := by
    rw [show 32 = value.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have htarget4 : Bytes.toB256
      (img4.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [img4]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    dsimp only [img3]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    dsimp only [img2]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact sliceAt img0 targetWord target
  have hnew4 : Bytes.toB256
      (img4.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp only [img4]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    dsimp only [img3]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact sliceAt img1 newPauserWord newPauser
  have hprevious4 : Bytes.toB256
      (img4.sliceD (previousPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [img4]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact sliceAt img2 previousPauserWord 0
  have hcontinuation4 : Bytes.toB256
      (img4.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    sliceAt img3 continuationWord 0
  dsimp only [registerMemory, registerImage]
  exact ⟨hwf4, hreads4, hsize4, htarget4, hnew4,
    hprevious4, hcontinuation4⟩

/-- Exact generated-runtime dispatcher reserve for
`registerPauser(address,address)`. -/
def registerPauserDispatchGas : Nat := 175

set_option maxRecDepth 16384 in
theorem registerPauser_dispatch_runCompiledTo
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (bodyGas G : Nat) (out : Execution)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hbody : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty, G + bodyGas⟩)
      (registerPauser dp) out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas + bodyGas⟩)
      (runtime dp) out ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  refine ⟨?_, ?_⟩
  · refine Prog.runCompiledTo_intro
      (mid := base.setMach ⟨[], Mem.empty, G + 174 + bodyGas⟩)
      (G := G + 174 + bodyGas) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, registerPauserDispatchGas,
        gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide +kernel
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide +kernel
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "registerPauser" [.address, .address] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (35) [0, 0,
        selector "registerPauser" [.address, .address],
        1, 1, 0, 0, 0, 1]
      case a =>
        have hboundary : G + 174 + bodyGas - 174 = G + bodyGas := by
          omega
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
          runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
          List.take, List.drop, List.head?, Option.map, Option.getD,
          linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

theorem registerPauserCalldata_spec (sevm : Sevm)
    (target newPauser : B256)
    (hdata : sevm.data = registerPauserCalldata target newPauser) :
    sevm.data.length.toB256 = 68 ∧
      Sevm.selector sevm =
        selector "registerPauser" [.address, .address] ∧
      Sevm.dataWord sevm 4 = target ∧
      Sevm.dataWord sevm 36 = newPauser := by
  constructor
  · rw [hdata]
    simp only [registerPauserCalldata, List.length_append,
      abiSelectorBytes_length, B256.length_toBytes]
    decide +kernel
  constructor
  · simp only [Sevm.selector, Sevm.dataWord, List.sliceD]
    rw [hdata]
    rw [show B256.toNat 0 = 0 from rfl, List.drop_zero,
      List.takeD_eq_take _ (by
        simp [registerPauserCalldata, abiSelectorBytes_length,
          B256.length_toBytes])]
    rw [registerPauserCalldata,
      show selector "registerPauser" [.address, .address] =
        (0x338d93fc : B256) by decide +kernel,
      show abiSelectorBytes (0x338d93fc : B256) =
        [0x33, 0x8d, 0x93, 0xfc] from rfl]
    simp only [B256.toBytes, B128.toBytes, UInt64.toBytes,
      UInt32.toBytes, UInt16.toBytes, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero]
    simp only [Bytes.toB256, Bytes.toB256_go_eight_cons]
    simp only [Bytes.toB256.go]
    change B256.shiftRight (⟨⟨_, _⟩, ⟨_, _⟩⟩ : B256) 224 = _
    simp only [B256.shiftRight]
    change (⟨0, B128.shiftRight ⟨_, _⟩ 96⟩ : B256) = _
    simp only [B128.shiftRight]
    norm_num [UInt64.ofBytes_eq_halves]
    congr 3
    rw [← UInt64.toNat_inj]
    have widen32 (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
    simp only [UInt64.toNat_shiftRight, UInt64.toNat_or,
      UInt64.toNat_shiftLeft_lo, widen32]
    norm_num
    rw [Nat.shiftRight_or_distrib]
    rw [Nat.shiftRight_eq_zero _ _ (UInt32.toNat_lt _)]
    decide +kernel
  constructor
  · apply dataWord_of_append
      (pre := abiSelectorBytes
        (selector "registerPauser" [.address, .address]))
      (w := target) (post := newPauser.toBytes)
    · rw [abiSelectorBytes_length]
      rfl
    · simpa [registerPauserCalldata] using hdata
  · apply dataWord_of_append
      (pre := abiSelectorBytes
        (selector "registerPauser" [.address, .address]) ++ target.toBytes)
      (w := newPauser) (post := [])
    · simp only [List.length_append, abiSelectorBytes_length,
        B256.length_toBytes]
      rfl
    · simpa [registerPauserCalldata] using hdata

/-- Clean settlement of an exact direct fresh-registration message retains
the raw successful poststate. -/
theorem registerPauser_success_settles_cleanly
    (dp : DeployParams) {msg : Msg} {ca : Adr}
    {final settled : Devm} {target newPauser : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = registerPauserCalldata target newPauser)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hclean : final.error.isNone = true) :
    settled = final := by
  have hsettle := (RunFrame.some_inv hprocess).2
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleError, processMessage.settle] at hsettle
  have hnotError : final.error.isSome ≠ true := by
    cases herror : final.error <;> simp_all
  rw [if_neg hnotError] at hsettle
  exact Except.ok.inj hsettle

/-- Any settled error of an exact direct registration message restores the
complete owner storage and transient storage from message entry. -/
theorem registerPauser_settled_error_restores_owner
    (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {target newPauser : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = registerPauserCalldata target newPauser)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    Devm.getStor post ca = msg.benv.state.getStor ca ∧
      post.transientStorage = msg.tenv.transientStorage := by
  have hrollback := ProcessMessage.rollback_of_error hprocess herror
  exact ⟨congrArg (fun state : State => state.getStor ca) hrollback.1,
    hrollback.2⟩

/-- At the exact top-level call boundary, an errored direct registration
message exposes no receipt log.  This does not claim raw `Devm.logs` erasure. -/
theorem registerPauser_settled_error_logs_eq_nil
    (dp : DeployParams) {msg : Msg} {state : State} {out : MsgCallOutput}
    {ca : Adr} {target newPauser : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = registerPauserCalldata target newPauser)
    (hrun : processMessageCall msg = .ok (state, out))
    (herror : out.error.isSome) :
    out.logs = [] :=
  processMessageCall_error_logs_eq_nil hrun herror

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

def lengthWritePost (sevm : Sevm) (base : Devm)
    (oldLength : B256) : Devm :=
  temporalSstorePost sevm base arrayLengthSlot oldLength

def indexClearPost (sevm : Sevm) (base : Devm)
    (target oldLength : B256) : Devm :=
  temporalSstorePost sevm
    (lengthWritePost sevm base oldLength)
    (indexSlot target) 0

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

def entryWritePost (sevm : Sevm) (base : Devm)
    (target next : B256) : Devm :=
  temporalSstorePost sevm base (arrayEntrySlot next) target

def indexWritePost (sevm : Sevm) (base : Devm)
    (target next : B256) : Devm :=
  temporalSstorePost sevm (entryWritePost sevm base target next)
    (indexSlot target) next

def entryClearPost (sevm : Sevm) (base : Devm)
    (target next : B256) : Devm :=
  temporalSstorePost sevm
    (indexWritePost sevm base target next)
    (arrayEntrySlot next) 0

/-! One-layer transport lemmas over an abstract base for the named removal
states.  Definitional transport across the nested `temporalSstorePost` tower
makes `whnf` unfold the base state at every layer and is measured to diverge;
peeling one named layer at a time by rewrite keeps every term small.  Use
these instead of `exact`/`change` across a tower or a `simp only` that
unfolds several `absentZero*Post` definitions at once. -/

theorem entryWritePost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (target next : B256) :
    (entryWritePost sevm base target next).accessedStorageKeys =
      base.accessedStorageKeys := rfl

theorem indexWritePost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (target next : B256) :
    (indexWritePost sevm base target next).accessedStorageKeys =
      base.accessedStorageKeys := rfl

theorem entryClearPost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (target next : B256) :
    (entryClearPost sevm base target next).accessedStorageKeys =
      base.accessedStorageKeys := rfl

theorem lengthWritePost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (oldLength : B256) :
    (lengthWritePost sevm base oldLength).accessedStorageKeys =
      base.accessedStorageKeys := rfl

theorem indexClearPost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (target oldLength : B256) :
    (indexClearPost sevm base target oldLength).accessedStorageKeys =
      base.accessedStorageKeys := rfl

theorem entryClearPost_logs
    (sevm : Sevm) (base : Devm) (target next : B256) :
    (entryClearPost sevm base target next).logs = base.logs := rfl

theorem indexClearPost_logs
    (sevm : Sevm) (base : Devm) (target oldLength : B256) :
    (indexClearPost sevm base target oldLength).logs = base.logs := rfl

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

/-- The degenerate `removeTarget` walk with an arbitrary `finishSetPauser`
continuation.  `removeTarget_runCompiled` below is the instance whose
continuation only appends the `PauserSet` record; a chronology whose
`registerAfterSet` arm also writes an expiry slot and emits a second record
instantiates this directly.

The staged image is bounded below and word-aligned, never fixed: all three
scratch windows the walk writes — the removed index, the array length and the
last target — charge whatever `calculateMemoryGasCost` difference the caller
supplies.  A register-side caller supplies `4` for the last-target window,
which is what a 640-to-704-byte image pays; an image that already covers 736
bytes supplies `0`. -/
theorem removeTarget_toFinish_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next : B256) (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost finishGas G : Nat)
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
      let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
      let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
      let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
      let tailPost := entryClearPost sevm base target next
      let removePost := indexClearPost sevm tailPost target oldLength
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, MLast, G + finishGas⟩)
        finishSetPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget post := by
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
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
  let tailPost := entryClearPost sevm base target next
  let removePost := indexClearPost sevm tailPost target oldLength
  have hstores := removeTarget_storePrefix_runCompiled
    dp sevm base MLast imgLast target oldLength next stack hstack
    arrayOriginal
    indexOriginal lengthOriginal holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost finishGas G hreadsLast htargetLast
    hremovedLast hlengthLast hlastLast
    htargetValid hnextNonzero hnextBound
    (by rw [hsizeLast]; exact Nat.le_max_right _ _) halignLast
    harray hindex
    hlength harrayOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost
    htailClearCost hlengthRestoreCost hindexClearCost hwarmArray hwarmIndex
    hwarmLength hsub hgasFinal hstatic post
    (by simpa only [MIndex, MLength, MLast,
      tailPost, removePost] using hfinish)
  let fs := (runtime dp).main :: (runtime dp).aux
  have hsaveLast : Func.RunCompiled fs sevm
      (base.setMach
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
      (base.setMach
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
  have hloadLastStorage : Func.RunCompiled fs sevm
      (base.setMach
        ⟨arrayKey :: stack, MLength,
          G + finishGas + 200 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
      (Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmArray
        (by simpa only [Devm.getStorVal_setMach, arrayKey] using harray)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by omega))
      hlastLoad
  have hlastTag : Func.RunCompiled fs sevm
      (base.setMach
        ⟨next :: stack, MLength,
          G + finishGas + 206 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
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
      have hg : G + finishGas + 206 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost - 6 =
          G + finishGas + 200 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost := by omega
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
      (base.setMach
        ⟨stack, MLength,
          G + finishGas + 212 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
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
      have hg : G + finishGas + 212 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost - 6 =
          G + finishGas + 206 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hlastTag
  have hsaveLength : Func.RunCompiled fs sevm
      (base.setMach
        ⟨arrayLengthWord * 32 :: next :: stack, MIndex,
          G + finishGas + 215 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
        (G := G + finishGas + 212 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost) (M := MLength) rfl
        (Devm.extCost_of_size
          (i := (arrayLengthWord * 32).toNat) (sz := 32) (e := lengthExtCost)
          hsizeIndex hlengthExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlastPrefix
  have hsaveLengthPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨next :: stack, MIndex,
          G + finishGas + 218 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      have hg : G + finishGas + 218 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 3 =
          G + finishGas + 215 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hsaveLength
  have hlengthLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨arrayLengthSlot :: stack, MIndex,
          G + finishGas + 318 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      post := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmLength
        (by simpa only [Devm.getStorVal_setMach] using hlength)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by omega))
      hsaveLengthPrefix
  have hlengthPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, MIndex,
          G + finishGas + 321 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      have hg : G + finishGas + 321 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 3 =
          G + finishGas + 318 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hlengthLoad
  have hsaveIndex : Func.RunCompiled fs sevm
      (base.setMach
        ⟨removedIndexWord * 32 :: next :: stack, M,
          G + finishGas + 324 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
        (G := G + finishGas + 321 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost + indexClearCost)
        (M := MIndex) rfl
        (Devm.extCost_of_size
          (i := (removedIndexWord * 32).toNat) (sz := 32) (e := indexExtCost)
          hsize hindexExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlengthPrefix
  have hsaveIndexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨next :: stack, M,
          G + finishGas + 327 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      have hg : G + finishGas + 327 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 3 =
          G + finishGas + 324 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hsaveIndex
  have hindexLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨indexKey :: stack, M,
          G + finishGas + 427 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      post := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmIndex
        (by simpa only [Devm.getStorVal_setMach, indexKey] using hindex)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by omega))
      hsaveIndexPrefix
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
  have hindexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, M,
          G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
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
    func_run (4) [3, indexKey]
    all_goals try {
      simpa [indexKey, indexSlot, slot] using
        congrArg (fun x : B256 => (regionWord indexRegion).or x)
          htargetValue }
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign htargetCovered]
      norm_num [gVerylow]
    case a =>
      rw [htargetMemory]
      have hg : G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 12 =
          G + finishGas + 427 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hindexLoad
  simp only [removeTarget]
  simpa only [fs, MLast] using hindexPrefix

/-- The degenerate `removeTarget` walk whose `finishSetPauser` continuation
only appends the `PauserSet` record: the removed target is already the array's
last entry, so the hole write, the moved entry's reverse-index repair and the
tail clear collapse onto one slot.  An instance of
`removeTarget_toFinish_runCompiled`. -/
theorem removeTarget_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next previous : B256) (stack : List B256)
    (hstack : stack.length ≤ 1)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost finishGas G : Nat)
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
    (hfinish :
      let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
      let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
      let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
      let tailPost := entryClearPost sevm base target next
      let removePost := indexClearPost sevm tailPost target oldLength
      let eventLog : Log :=
        ⟨sevm.currentTarget, [pauserSetEvent, target, previous, 0], []⟩
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, MLast, G + finishGas⟩)
        finishSetPauser
        ((removePost.addLog eventLog).setMach ⟨stack, MLast, G⟩)) :
    let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, previous, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget
      (((indexClearPost sevm
          (entryClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨stack, MLast, G⟩) := by
  dsimp only
  exact removeTarget_toFinish_runCompiled dp sevm base M img target oldLength
    next stack hstack arrayOriginal indexOriginal lengthOriginal holeCost
    movedIndexCost tailClearCost lengthRestoreCost indexClearCost finishGas G
    hwf hreads htarget htargetValid hnextNonzero hnextBound entrySize
    indexExtCost lengthExtCost lastExtCost hsize halign hentryLow hindexExtCost
    hlengthExtCost hlastExtCost harray hindex hlength harrayOrig hindexOrig
    hlengthOrig
    hholeCost hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    hwarmArray hwarmIndex hwarmLength hsub hgasFinal hstatic _ hfinish

/-! ## The general swap-and-pop removal walk

`removeTarget_runCompiled` above walks the removal of a target that is already
the array's last entry, where the hole write, the moved entry's reverse-index
repair and the tail clear all land on one slot.  The declarations below walk
the same `removeTarget` code for a removed target that is *not* last: the hole
`arrayEntrySlot idx`, the moved entry's index `indexSlot lastTarget`, the tail
`arrayEntrySlot len`, `arrayLengthSlot` and `indexSlot target` are five
distinct keys, and every later read is taken out of the poststate of the write
before it.  No disjointness is hypothesized: `idx ≠ len` and
`lastTarget ≠ target` plus the payload bounds derive all ten pairs. -/

/-- Poststate of the general swap-pop's three array-region writes: the hole
write `arrayEntrySlot idx := lastTarget`, the moved entry's reverse-index
repair `indexSlot lastTarget := idx`, and the tail clear
`arrayEntrySlot len := 0`.  Taking `lastTarget := target` and `len := idx`
recovers `entryClearPost`, the degenerate walk's poststate. -/
def swapPopClearPost (sevm : Sevm) (base : Devm)
    (lastTarget idx len : B256) : Devm :=
  temporalSstorePost sevm
    (indexWritePost sevm base lastTarget idx)
    (arrayEntrySlot len) 0

theorem swapPopClearPost_eq_entryClearPost
    (sevm : Sevm) (base : Devm) (target next : B256) :
    swapPopClearPost sevm base target next next =
      entryClearPost sevm base target next := rfl

theorem swapPopClearPost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (lastTarget idx len : B256) :
    (swapPopClearPost sevm base lastTarget idx len).accessedStorageKeys =
      base.accessedStorageKeys := rfl

theorem swapPopClearPost_logs
    (sevm : Sevm) (base : Devm) (lastTarget idx len : B256) :
    (swapPopClearPost sevm base lastTarget idx len).logs = base.logs := rfl

/-- The five stores of a general swap-pop, from the scratch words already
holding the removed index, the array length and the moved target. -/
private theorem removeTarget_swapPop_storePrefix_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost finishGas G : Nat)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hremovedWord : Bytes.toB256
      (img.sliceD (removedIndexWord * 32).toNat 32 0) = idx)
    (hlengthWord : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = len)
    (hlastWord : Bytes.toB256
      (img.sliceD (lastTargetWord * 32).toNat 32 0) = lastTarget)
    (htargetValid : nonzeroCanonicalAddress target)
    (hlastValid : canonicalAddress lastTarget)
    (hlastNe : lastTarget ≠ target)
    (hidxNonzero : idx ≠ 0) (hidxBound : idx.toNat < 2 ^ 252)
    (hlenNonzero : len ≠ 0) (hlenBound : len.toNat < 2 ^ 252)
    (hidxNeLen : idx ≠ len)
    (hsize : 736 ≤ M.size) (halign : M.size % 32 = 0)
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
    (hsub : len - 1 = oldLength)
    (hgasFinal : gCallStipend < G + finishGas + 12 + indexClearCost)
    (hstatic : sevm.isStatic = false)
    (post : Devm)
    (hfinish :
      let tailPost := swapPopClearPost sevm base lastTarget idx len
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
  let holeKey := arrayEntrySlot idx
  let movedKey := indexSlot lastTarget
  let tailKey := arrayEntrySlot len
  let indexKey := indexSlot target
  let holePost := entryWritePost sevm base lastTarget idx
  let movedPost := indexWritePost sevm base lastTarget idx
  let tailPost := swapPopClearPost sevm base lastTarget idx len
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
  have hmovedHolePost : holePost.getStorVal sevm.currentTarget movedKey =
      movedCurrent := by
    rw [show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl]
    rw [temporalSstorePost_other sevm base holeKey lastTarget
      sevm.currentTarget movedKey (pairNe hmovedHole)]
    exact hmoved
  have htailMovedPost : movedPost.getStorVal sevm.currentTarget tailKey =
      lastTarget := by
    rw [show movedPost = temporalSstorePost sevm holePost movedKey idx by rfl]
    rw [temporalSstorePost_other sevm holePost movedKey idx
      sevm.currentTarget tailKey (pairNe hmovedTailNe.symm)]
    rw [show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl]
    rw [temporalSstorePost_other sevm base holeKey lastTarget
      sevm.currentTarget tailKey (pairNe htailHole)]
    exact htail
  have hlengthTailPost : tailPost.getStorVal sevm.currentTarget
      arrayLengthSlot = len := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 by rfl]
    rw [temporalSstorePost_other sevm movedPost tailKey 0
      sevm.currentTarget arrayLengthSlot (pairNe hlengthTailNe)]
    rw [show movedPost = temporalSstorePost sevm holePost movedKey idx by rfl]
    rw [temporalSstorePost_other sevm holePost movedKey idx
      sevm.currentTarget arrayLengthSlot (pairNe hmovedLength.symm)]
    rw [show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl]
    rw [temporalSstorePost_other sevm base holeKey lastTarget
      sevm.currentTarget arrayLengthSlot (pairNe hlengthHole)]
    exact hlength
  have hindexTailPost : tailPost.getStorVal sevm.currentTarget indexKey =
      idx := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 by rfl]
    rw [temporalSstorePost_other sevm movedPost tailKey 0
      sevm.currentTarget indexKey (pairNe hindexTailNe)]
    rw [show movedPost = temporalSstorePost sevm holePost movedKey idx by rfl]
    rw [temporalSstorePost_other sevm holePost movedKey idx
      sevm.currentTarget indexKey (pairNe hindexMovedNe)]
    rw [show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl]
    rw [temporalSstorePost_other sevm base holeKey lastTarget
      sevm.currentTarget indexKey (pairNe hindexHoleNe)]
    exact hindex
  have hwarmMovedHole : (sevm.currentTarget, movedKey) ∈
      holePost.accessedStorageKeys := by
    rw [show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmMoved
  have hwarmTailMoved : (sevm.currentTarget, tailKey) ∈
      movedPost.accessedStorageKeys := by
    rw [show movedPost = temporalSstorePost sevm holePost movedKey idx by rfl,
      temporalSstorePost_accessedStorageKeys,
      show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmTail
  have hwarmLengthTail : (sevm.currentTarget, arrayLengthSlot) ∈
      tailPost.accessedStorageKeys := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 by rfl,
      temporalSstorePost_accessedStorageKeys,
      show movedPost = temporalSstorePost sevm holePost movedKey idx by rfl,
      temporalSstorePost_accessedStorageKeys,
      show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmLength
  have hwarmIndexTail : (sevm.currentTarget, indexKey) ∈
      tailPost.accessedStorageKeys := by
    rw [show tailPost = temporalSstorePost sevm movedPost tailKey 0 by rfl,
      temporalSstorePost_accessedStorageKeys,
      show movedPost = temporalSstorePost sevm holePost movedKey idx by rfl,
      temporalSstorePost_accessedStorageKeys,
      show holePost = temporalSstorePost sevm base holeKey lastTarget by rfl,
      temporalSstorePost_accessedStorageKeys]
    exact hwarmIndex
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
  have hremovedMemory := readMemory removedIndexWord (by decide)
  have hlengthMemory := readMemory arrayLengthWord (by decide)
  have hlastMemory := readMemory lastTargetWord (by decide)
  have hremovedValue := readValue removedIndexWord idx hremovedWord
  have hlengthValue := readValue arrayLengthWord len hlengthWord
  have hlastValue := readValue lastTargetWord lastTarget hlastWord
  have hrestore := removeTarget_restoreTail_runCompiled
    dp sevm tailPost M img target oldLength len idx 0 stack hstack
    lengthOriginal indexOriginal lengthRestoreCost indexClearCost finishGas G
    hreads htarget hlengthWord htargetValid hsize halign hlengthTailPost
    hindexTailPost hlengthOrig hindexOrig hlengthRestoreCost hindexClearCost
    hwarmLengthTail hwarmIndexTail hsub hgasFinal hstatic post
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
        ⟨tailKey :: 0 :: stack, M,
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
        ⟨len :: 0 :: stack, M,
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
        ⟨movedKey :: idx :: stack, M,
          G + finishGas + 58 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost⟩)
      (Ninst.sstore ::: pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord arrayLengthWord +++
        pushB256 1 ::: swap 0 ::: sub ::: pushB256 arrayLengthSlot :::
        Ninst.sstore ::: pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hmovedHolePost hmovedOrig hmovedIndexCost
        hwarmMovedHole (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      htailPrefix
  have hmovedTag : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨lastTarget :: idx :: stack, M,
          G + finishGas + 64 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost⟩)
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
          tailClearCost + movedIndexCost - 6 =
          G + finishGas + 58 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost := by omega
      rw [hg]
      exact hstoreMoved
  have hmovedLast : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨idx :: stack, M,
          G + finishGas + 70 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost⟩)
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
          G + finishGas + 76 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost⟩)
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
        ⟨holeKey :: lastTarget :: stack, M,
          G + finishGas + 76 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost⟩)
      (Ninst.sstore ::: loadWord removedIndexWord +++
        loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hhole hholeOrig hholeCost hwarmHole
        (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      hmovedPrefix
  have hholeTag : Func.RunCompiled fs sevm
      (base.setMach
        ⟨idx :: lastTarget :: stack, M,
          G + finishGas + 82 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost⟩)
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
          tailClearCost + movedIndexCost + holeCost - 6 =
          G + finishGas + 76 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost := by omega
      rw [hg]
      exact hstoreHole
  have hholeRemoved : Func.RunCompiled fs sevm
      (base.setMach
        ⟨lastTarget :: stack, M,
          G + finishGas + 88 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost⟩)
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
          G + finishGas + 94 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost⟩)
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
  have hg : G + finishGas + 94 + lengthRestoreCost + indexClearCost +
      tailClearCost + movedIndexCost + holeCost =
      G + finishGas + 94 + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost := by omega
  rw [hg] at hholePrefix
  simpa only [lastTargetIndexKey, prepend_append, fs,
    holeKey, movedKey, tailKey, indexKey, holePost, movedPost,
    tailPost] using hholePrefix

/-- The general swap-and-pop `removeTarget` walk: the removed target's index is
`idx`, the array's last entry is `lastTarget` at `len`, and `idx ≠ len` with
`lastTarget ≠ target`, so the hole write, the moved entry's reverse-index
repair, the tail clear, the length decrement and the index clear land on five
distinct storage keys.  `removeTarget_runCompiled` is the sibling degenerate
walk, where the removed target is already last and those keys collapse; neither
statement is an instance of the other.  Its memory window is parameterized the
same way: bounded below, word-aligned, and charging the caller-supplied
expansion cost for each of the three scratch words. -/
theorem removeTarget_swapPop_toFinish_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost finishGas G : Nat)
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
    (hsub : len - 1 = oldLength)
    (hgasFinal : gCallStipend < G + finishGas + 12 + indexClearCost)
    (hstatic : sevm.isStatic = false)
    (post : Devm)
    (hfinish :
      let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
      let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
      let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
      let tailPost := swapPopClearPost sevm base lastTarget idx len
      let removePost := indexClearPost sevm tailPost target oldLength
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, MLast, G + finishGas⟩)
        finishSetPauser post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget post := by
  let tailKey := arrayEntrySlot len
  let indexKey := indexSlot target
  let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    idx.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    len.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    lastTarget.toBytes
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
  let tailPost := swapPopClearPost sevm base lastTarget idx len
  let removePost := indexClearPost sevm tailPost target oldLength
  have hstores := removeTarget_swapPop_storePrefix_runCompiled
    dp sevm base MLast imgLast target lastTarget idx len oldLength
    stack hstack holeCurrent movedCurrent
    holeOriginal movedOriginal tailOriginal lengthOriginal indexOriginal
    holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost finishGas G hreadsLast htargetLast
    hremovedLast hlengthLast hlastLast
    htargetValid hlastValid hlastNe hidxNonzero hidxBound hlenNonzero
    hlenBound hidxNeLen (by rw [hsizeLast]; exact Nat.le_max_right _ _)
    halignLast
    hhole hmoved htail hindex hlength
    hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig
    hholeCost hmovedIndexCost
    htailClearCost hlengthRestoreCost hindexClearCost
    hwarmHole hwarmMoved hwarmTail hwarmIndex
    hwarmLength hsub hgasFinal hstatic post
    (by simpa only [MIndex, MLength, MLast,
      tailPost, removePost] using hfinish)
  let fs := (runtime dp).main :: (runtime dp).aux
  have hsaveLast : Func.RunCompiled fs sevm
      (base.setMach
        ⟨lastTargetWord * 32 :: lastTarget :: stack, MLength,
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
      (base.setMach
        ⟨lastTarget :: stack, MLength,
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
  have hloadLastStorage : Func.RunCompiled fs sevm
      (base.setMach
        ⟨tailKey :: stack, MLength,
          G + finishGas + 200 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
      (Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      post := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmTail
        (by simpa only [Devm.getStorVal_setMach, tailKey] using htail)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by omega))
      hlastLoad
  have hlastTag : Func.RunCompiled fs sevm
      (base.setMach
        ⟨len :: stack, MLength,
          G + finishGas + 206 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
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
      have hg : G + finishGas + 206 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost - 6 =
          G + finishGas + 200 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hloadLastStorage
  have hlengthValue :
      (MLength.read (arrayLengthWord * 32).toNat 32).1.toB256 = len := by
    rw [Mem.Reads.read hreadsLength]
    dsimp only [imgLength]
    rw [show 32 = len.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hlengthMemory :
      (MLength.read (arrayLengthWord * 32).toNat 32).2 = MLength := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halignLength (by
      rw [hsizeLength, show (arrayLengthWord * 32).toNat + 32 = 704 by decide]
      exact Nat.le_max_right _ _))]
  have hlastPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, MLength,
          G + finishGas + 212 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost⟩)
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
      have hg : G + finishGas + 212 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost - 6 =
          G + finishGas + 206 + lastExtCost + holeCost + movedIndexCost +
            tailClearCost + lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hlastTag
  have hsaveLength : Func.RunCompiled fs sevm
      (base.setMach
        ⟨arrayLengthWord * 32 :: len :: stack, MIndex,
          G + finishGas + 215 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
        (G := G + finishGas + 212 + lastExtCost + holeCost + movedIndexCost +
          tailClearCost + lengthRestoreCost + indexClearCost) (M := MLength) rfl
        (Devm.extCost_of_size
          (i := (arrayLengthWord * 32).toNat) (sz := 32) (e := lengthExtCost)
          hsizeIndex hlengthExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlastPrefix
  have hsaveLengthPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨len :: stack, MIndex,
          G + finishGas + 218 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      have hg : G + finishGas + 218 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 3 =
          G + finishGas + 215 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hsaveLength
  have hlengthLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨arrayLengthSlot :: stack, MIndex,
          G + finishGas + 318 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      post := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmLength
        (by simpa only [Devm.getStorVal_setMach] using hlength)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by omega))
      hsaveLengthPrefix
  have hlengthPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, MIndex,
          G + finishGas + 321 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      have hg : G + finishGas + 321 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 3 =
          G + finishGas + 318 + lastExtCost + lengthExtCost + holeCost +
            movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hlengthLoad
  have hsaveIndex : Func.RunCompiled fs sevm
      (base.setMach
        ⟨removedIndexWord * 32 :: idx :: stack, M,
          G + finishGas + 324 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
        (G := G + finishGas + 321 + lastExtCost + lengthExtCost + holeCost +
          movedIndexCost + tailClearCost + lengthRestoreCost + indexClearCost)
        (M := MIndex) rfl
        (Devm.extCost_of_size
          (i := (removedIndexWord * 32).toNat) (sz := 32) (e := indexExtCost)
          hsize hindexExtCost)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlengthPrefix
  have hsaveIndexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨idx :: stack, M,
          G + finishGas + 327 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      have hg : G + finishGas + 327 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 3 =
          G + finishGas + 324 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hsaveIndex
  have hindexLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨indexKey :: stack, M,
          G + finishGas + 427 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost⟩)
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
      post := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmIndex
        (by simpa only [Devm.getStorVal_setMach, indexKey] using hindex)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by omega))
      hsaveIndexPrefix
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
  have hindexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, M,
          G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
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
    func_run (4) [3, indexKey]
    all_goals try {
      simpa [indexKey, indexSlot, slot] using
        congrArg (fun x : B256 => (regionWord indexRegion).or x)
          htargetValue }
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign htargetCovered]
      norm_num [gVerylow]
    case a =>
      rw [htargetMemory]
      have hg : G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost - 12 =
          G + finishGas + 427 + lastExtCost + indexExtCost + lengthExtCost +
            holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
            indexClearCost := by omega
      rw [hg]
      exact hindexLoad
  simp only [removeTarget]
  simpa only [fs, MLast] using hindexPrefix

/-- The general swap-and-pop `removeTarget` walk whose `finishSetPauser`
continuation only appends the `PauserSet` record.  An instance of
`removeTarget_swapPop_toFinish_runCompiled`. -/
theorem removeTarget_swapPop_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target lastTarget idx len oldLength previous : B256)
    (stack : List B256)
    (hstack : stack.length ≤ 1)
    (holeCurrent movedCurrent : B256)
    (holeOriginal movedOriginal tailOriginal lengthOriginal
      indexOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost finishGas G : Nat)
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
    (hsub : len - 1 = oldLength)
    (hgasFinal : gCallStipend < G + finishGas + 12 + indexClearCost)
    (hstatic : sevm.isStatic = false)
    (hfinish :
      let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
      let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
      let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
      let tailPost := swapPopClearPost sevm base lastTarget idx len
      let removePost := indexClearPost sevm tailPost target oldLength
      let eventLog : Log :=
        ⟨sevm.currentTarget, [pauserSetEvent, target, previous, 0], []⟩
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (removePost.setMach ⟨stack, MLast, G + finishGas⟩)
        finishSetPauser
        ((removePost.addLog eventLog).setMach ⟨stack, MLast, G⟩)) :
    let MIndex := M.write (removedIndexWord * 32).toNat idx.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat len.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat lastTarget.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, previous, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget
      (((indexClearPost sevm
          (swapPopClearPost sevm base lastTarget idx len)
          target oldLength).addLog eventLog).setMach
        ⟨stack, MLast, G⟩) := by
  dsimp only
  exact removeTarget_swapPop_toFinish_runCompiled dp sevm base M img target
    lastTarget idx len oldLength stack hstack holeCurrent movedCurrent
    holeOriginal movedOriginal tailOriginal lengthOriginal indexOriginal
    holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost
    finishGas G hwf hreads htarget htargetValid hlastValid hlastNe hidxNonzero
    hidxBound hlenNonzero hlenBound hidxNeLen entrySize indexExtCost
    lengthExtCost lastExtCost hsize halign hentryLow hindexExtCost
    hlengthExtCost hlastExtCost hhole hmoved htail hindex hlength hholeOrig
    hmovedOrig
    htailOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
    hlengthRestoreCost hindexClearCost hwarmHole hwarmMoved hwarmTail
    hwarmIndex hwarmLength hsub hgasFinal hstatic _ hfinish

/-- The three Registry cells mutated by append/remove are restored exactly to
their append-entry values. -/
private theorem appendTarget_absentZero_registry_cells_restored
    (sevm : Sevm) (base : Devm) (target oldLength next : B256)
    (htargetValid : canonicalAddress target)
    (hnextNonzero : next ≠ 0)
    (hnextBound : next.toNat < 2 ^ 252)
    (harray : base.getStorVal sevm.currentTarget
      (arrayEntrySlot next) = 0)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = 0)
    (hlength : base.getStorVal sevm.currentTarget
      arrayLengthSlot = oldLength) :
    let lengthBase := temporalSloadBase sevm base arrayLengthSlot
    let arrayPost := temporalSstorePost sevm lengthBase
      (arrayEntrySlot next) target
    let indexPost := temporalSstorePost sevm arrayPost
      (indexSlot target) next
    let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
    let finalStorage := indexClearPost sevm
      (entryClearPost sevm lengthPost target next)
      target oldLength
    finalStorage.getStorVal sevm.currentTarget (arrayEntrySlot next) =
        base.getStorVal sevm.currentTarget (arrayEntrySlot next) ∧
      finalStorage.getStorVal sevm.currentTarget (indexSlot target) =
        base.getStorVal sevm.currentTarget (indexSlot target) ∧
      finalStorage.getStorVal sevm.currentTarget arrayLengthSlot =
        base.getStorVal sevm.currentTarget arrayLengthSlot := by
  dsimp only
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  have harrayFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid htargetValid hnextBound
  have hlengthFamilies := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid htargetValid
  have hlengthArray :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnextNonzero hnextBound
  have pairNe {left right : B256} (h : left ≠ right) :
      (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  constructor
  · simp only [indexClearPost, lengthWritePost,
      entryClearPost, indexWritePost, entryWritePost]
    rw [temporalSstorePost_other _ _ indexKey 0 _ arrayKey
        (pairNe (Ne.symm harrayFamilies.2.1)),
      temporalSstorePost_other _ _ arrayLengthSlot oldLength _ arrayKey
        (pairNe (Ne.symm hlengthArray)),
      temporalSstorePost_self]
    exact harray.symm
  constructor
  · simp only [indexClearPost]
    rw [temporalSstorePost_self]
    exact hindex.symm
  · simp only [indexClearPost, lengthWritePost]
    rw [temporalSstorePost_other _ _ indexKey 0 _ arrayLengthSlot
        (pairNe (Ne.symm hlengthFamilies.2.1)),
      temporalSstorePost_self]
    exact hlength.symm

/-- The four scratch writes `registerPauser`'s body performs before entering
the kernel: the two decoded arguments and the two zero words.

The staging is chronology-independent — it happens before `setPauserKernel`
is entered and does not depend on which Registry branch the kernel takes — so
the kernel run is taken as a hypothesis and every chronology leaf shares this
one walk. -/
theorem registerPauser_stageArgs_runCompiled
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

end Blanc.LidoCircuitBreaker
