import Blanc.LidoCircuitBreakerPauseWalk
import Blanc.LidoCircuitBreakerPauseOkRoute
import Blanc.TransientInvariance

/-!
# What is already true before the target gets control

Every Stage 5 statement about the pause was proved at a world with a
cooperative callee.  Some facts about a pause do not depend on the callee at
all, because they are settled **before the target ever executes**: `pause`
takes the reentrancy lock, checks the caller's assignment and liveness, and
runs the whole `setPauser` kernel — clearing the paused target's assignment
and emitting `PauserSet` — and only then reaches `pauseAfterSet`, which
performs the external CALL and STATICCALL.

The theorems here are about that prefix, and they are stated over an arbitrary
`base` world, an arbitrary target and arbitrary target bytecode: no hypothesis
below constrains the code at the paused address, and none can be discharged
only by a cooperating callee.

## What these do not say

* Nothing about what the target does, returns, or leaves behind.
* Nothing about the pause completing, succeeding, or reaching its expiry
  write.  A hostile callee can prevent all of that, and the published
  callback-visible liveness counterexample stands unchanged.
* Nothing about the CALL's arguments or the decoding of the target's answer.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The lock is held for the whole of the rest of the pause

`pause` opens `tload lockKey ::: iszero ::: (…taken… <?> …refuse…)`, so the
first thing a successful pause does is write `1` to the lock, and every state
downstream of `pauseLockPost` inherits it. -/

/-- Transient read-after-write at the same address and key.  The zero-valued
special case is transcribed privately in
`Blanc/LidoCircuitBreakerPauseWorldRun.lean`; this general form is the one the
pre-control statements need, and it is an upstream candidate. -/
theorem getTransVal_setTransVal_self (devm : Devm) (a : Adr) (k v : B256) :
    (devm.setTransVal a k v).getTransVal a k = v := by
  show ((devm.transientStorage.setStorVal a k v).getD a .empty).get k = v
  unfold Tra.setStorVal
  rw [Std.TreeMap.getD_eq_getD_getElem?, Tra.getElem?_set, if_pos rfl]
  split
  · -- The pruning branch: the map after the write is empty, so the write's
    -- own read-back law already says the stored word is what an empty map
    -- reads at `k`.
    rename_i hpruned
    have hEmpty :
        (Std.TreeMap.getD devm.transientStorage a Stor.empty).set k v =
          Stor.empty :=
      Std.TreeMap.eq_empty_iff_isEmpty.mpr hpruned
    have hread := Stor.get_set_self
      (Std.TreeMap.getD devm.transientStorage a Stor.empty) k v
    rw [hEmpty] at hread
    exact hread
  · show ((Option.getD (some _)) Stor.empty).get k = v
    exact Stor.get_set_self _ _ _

/-- The lock is set at the state `pause` hands to its own body. -/
theorem pauseLockPost_lock (sevm : Sevm) (base : Devm) :
    (pauseLockPost sevm base).getTransVal sevm.currentTarget lockKey = 1 :=
  getTransVal_setTransVal_self _ _ _ _

/-! ## The lock survives to the kernel entry

`pause`'s three reads between taking the lock and entering the `setPauser`
kernel are `SLOAD`s.  A cold `SLOAD` only warms an accessed-key set, so none
of them touches transient storage and the lock is still held at the state the
kernel is entered from. -/

theorem temporalSloadBase_getTransVal (sevm : Sevm) (base : Devm)
    (key : B256) (a : Adr) (k : B256) :
    (temporalSloadBase sevm base key).getTransVal a k =
      base.getTransVal a k := by
  unfold temporalSloadBase
  split
  · rfl
  · rfl

/-- The lock is held at the state `pause` hands the Registry kernel. -/
theorem pauseKernelBase_lock (sevm : Sevm) (base : Devm)
    (target pauser : B256) :
    (pauseKernelBase sevm base target pauser).getTransVal
      sevm.currentTarget lockKey = 1 := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getTransVal, temporalSloadBase_getTransVal,
    temporalSloadBase_getTransVal]
  exact pauseLockPost_lock sevm base

/-! ## The assignment is cleared before the kernel branches

`setPauserKernel` reads the target's assignment cell and immediately writes
`newPauserWord` into it, *before* the branch that separates the append arm
from the two removal arms.  `assignmentPost` is the substrate's name for that
post-write state, so the clearing is a fact about a named state on the common
prefix of every arm — no arm analysis is needed to establish it. -/

/-- Storage read-after-write at the same address and key.  Another upstream
candidate: the substrate uses this shape repeatedly but through per-site
rewrites rather than a named law. -/
theorem Devm.getStorVal_setStorVal_self (devm : Devm) (a : Adr) (k v : B256) :
    (devm.setStorVal a k v).getStorVal a k = v := by
  show ((devm.state.setStorVal a k v).get a).stor.get k = v
  unfold State.setStorVal
  rw [State.get_set_self]
  exact Stor.get_set_self _ _ _

theorem temporalSstorePost_getStorVal_self (sevm : Sevm) (base : Devm)
    (key value : B256) :
    (temporalSstorePost sevm base key value).getStorVal
      sevm.currentTarget key = value := by
  unfold temporalSstorePost
  exact Devm.getStorVal_setStorVal_self _ _ _ _

/-- The kernel's assignment write, read back.  For a pause this is invoked
with `newPauser = 0`, which is the clearing this goal is about; the statement
is left general because the same write serves registration. -/
theorem assignmentPost_assignment (sevm : Sevm) (base : Devm)
    (target newPauser : B256) :
    (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (assignmentSlot target) = newPauser :=
  temporalSstorePost_getStorVal_self _ _ _ _

/-! ## The clearing survives to the boundary

Between the kernel's assignment write and the `pauseAfterSet` entry a pause
crosses the old pauser's count decrement and `removeTarget`'s five `SSTORE`s,
and then emits `PauserSet`.  None of those six writes is in the assignment
region, and the log is not a write at all.

Both removal walks hand `finishSetPauser` a state the substrate names:
`removeTarget_swapPop_toFinish_runCompiled` binds it as `indexClearPost sevm
(swapPopClearPost sevm base lastTarget idx len) target oldLength`, and the
degenerate walk's `entryClearPost sevm base target next` is the
`lastTarget := target`, `idx = len := next` instance of `swapPopClearPost`
(`swapPopClearPost_eq_entryClearPost`).  One frame therefore serves both.

The transports below peel one named layer at a time.  Crossing the tower
definitionally instead makes `whnf` unfold the base state at every layer and
is measured to diverge; the substrate records that discipline beside its
`accessedStorageKeys` and `logs` transports, which is where these would have
lived had a `getStorVal` transport existed. -/

private theorem pairNe {sevm : Sevm} {left right : B256} (h : left ≠ right) :
    (sevm.currentTarget, left) ≠ (sevm.currentTarget, right) :=
  fun hp => h (congrArg Prod.snd hp)

theorem entryWritePost_getStorVal_other (sevm : Sevm) (base : Devm)
    (target next key : B256) (hne : key ≠ arrayEntrySlot next) :
    (entryWritePost sevm base target next).getStorVal sevm.currentTarget key =
      base.getStorVal sevm.currentTarget key := by
  unfold entryWritePost
  exact temporalSstorePost_other _ _ _ _ _ _ (pairNe hne)

theorem indexWritePost_getStorVal_other (sevm : Sevm) (base : Devm)
    (target next key : B256) (hentry : key ≠ arrayEntrySlot next)
    (hindex : key ≠ indexSlot target) :
    (indexWritePost sevm base target next).getStorVal sevm.currentTarget key =
      base.getStorVal sevm.currentTarget key := by
  unfold indexWritePost
  rw [temporalSstorePost_other _ _ _ _ _ _ (pairNe hindex)]
  exact entryWritePost_getStorVal_other sevm base target next key hentry

theorem swapPopClearPost_getStorVal_other (sevm : Sevm) (base : Devm)
    (lastTarget idx len key : B256)
    (hmoved : key ≠ arrayEntrySlot idx)
    (hlastIndex : key ≠ indexSlot lastTarget)
    (htail : key ≠ arrayEntrySlot len) :
    (swapPopClearPost sevm base lastTarget idx len).getStorVal
      sevm.currentTarget key = base.getStorVal sevm.currentTarget key := by
  unfold swapPopClearPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (pairNe htail)]
  exact indexWritePost_getStorVal_other sevm base lastTarget idx key hmoved
    hlastIndex

theorem lengthWritePost_getStorVal_other (sevm : Sevm) (base : Devm)
    (oldLength key : B256) (hne : key ≠ arrayLengthSlot) :
    (lengthWritePost sevm base oldLength).getStorVal sevm.currentTarget key =
      base.getStorVal sevm.currentTarget key := by
  unfold lengthWritePost
  exact temporalSstorePost_other _ _ _ _ _ _ (pairNe hne)

theorem indexClearPost_getStorVal_other (sevm : Sevm) (base : Devm)
    (target oldLength key : B256) (hlength : key ≠ arrayLengthSlot)
    (hindex : key ≠ indexSlot target) :
    (indexClearPost sevm base target oldLength).getStorVal
      sevm.currentTarget key = base.getStorVal sevm.currentTarget key := by
  unfold indexClearPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (pairNe hindex)]
  exact lengthWritePost_getStorVal_other sevm base oldLength key hlength

/-- The storage frame of `removeTarget`'s whole span, at the altitude both
removal walks hand `finishSetPauser`: a cell missing all five written keys
reads the same after the span as before it. -/
theorem removalPost_getStorVal_other (sevm : Sevm) (base : Devm)
    (target lastTarget idx len oldLength key : B256)
    (hmoved : key ≠ arrayEntrySlot idx)
    (hlastIndex : key ≠ indexSlot lastTarget)
    (htail : key ≠ arrayEntrySlot len)
    (hlength : key ≠ arrayLengthSlot)
    (hindex : key ≠ indexSlot target) :
    (indexClearPost sevm (swapPopClearPost sevm base lastTarget idx len)
        target oldLength).getStorVal sevm.currentTarget key =
      base.getStorVal sevm.currentTarget key := by
  rw [indexClearPost_getStorVal_other _ _ _ _ _ hlength hindex]
  exact swapPopClearPost_getStorVal_other sevm base lastTarget idx len key
    hmoved hlastIndex htail

/-! ### From the kernel's write to the boundary

The remaining two layers are the old pauser's count decrement, which
`foundKernelPost` names, and `finishSetPauser`'s `PauserSet` record, which is
not a storage write at all. -/

/-- The assignment cell survives the old pauser's count decrement. -/
theorem foundKernelPost_assignment (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount : B256)
    (hne : assignmentSlot target ≠ countSlot oldPauser) :
    (foundKernelPost sevm base target newPauser oldPauser oldCount).getStorVal
      sevm.currentTarget (assignmentSlot target) = newPauser := by
  unfold foundKernelPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (pairNe hne),
    temporalSloadBase_getStorVal]
  exact assignmentPost_assignment sevm base target newPauser

/-- Emitting a record and re-seating the machine word are not storage writes. -/
theorem addLog_setMach_getStorVal (devm : Devm) (l : Log) (m : Mach)
    (a : Adr) (key : B256) :
    ((devm.addLog l).setMach m).getStorVal a key = devm.getStorVal a key := rfl

/-- **P1.**  At the state `pause` hands to `pauseAfterSet` — the state at which
the target first receives control — the paused target's assignment cell is
`0`.

Nothing here constrains the code at `target` or at any other address: `base` is
an arbitrary `Devm`, so whatever bytecode sits at the paused address sits there
in this statement too, and no hypothesis below could be discharged by a
cooperating callee and not by a hostile one.  The premises are the payload
bounds the Registry's region tagging needs — the addresses are canonical and
the two array indices fit under the tag — and nothing else.

The state is the one the substrate's own removal walks name: `base` is
`removeTarget`'s entry state, `swapPopClearPost … lastTarget idx len` its five
writes, `indexClearPost` the length restore and index clear, and the `addLog`
`finishSetPauser`'s `PauserSet` record.  The degenerate already-last walk is
the `lastTarget := target`, `idx = len := next` instance of the same tower.

This says nothing about the pause completing.  A hostile target can prevent
that outright, and the published callback-visible liveness counterexample
stands. -/
theorem pauseAfterSetEntry_assignment (sevm : Sevm) (base : Devm)
    (target oldPauser oldCount lastTarget idx len oldLength : B256)
    (l : Log) (m : Mach)
    (htarget : canonicalAddress target)
    (hlastTarget : canonicalAddress lastTarget)
    (holdPauser : canonicalAddress oldPauser)
    (hidx : idx.toNat < 2 ^ 252)
    (hlen : len.toNat < 2 ^ 252) :
    (((indexClearPost sevm
          (swapPopClearPost sevm
            (foundKernelPost sevm base target 0 oldPauser oldCount)
            lastTarget idx len)
          target oldLength).addLog l).setMach m).getStorVal
      sevm.currentTarget (assignmentSlot target) = 0 := by
  have hmoved : assignmentSlot target ≠ arrayEntrySlot idx :=
    (registryAddressFamilies_ne_arrayEntrySlot htarget holdPauser hidx).1
  have htail : assignmentSlot target ≠ arrayEntrySlot len :=
    (registryAddressFamilies_ne_arrayEntrySlot htarget holdPauser hlen).1
  have hlength : assignmentSlot target ≠ arrayLengthSlot :=
    (registryAddressFamilies_ne_arrayLengthSlot htarget holdPauser).1
  have hlastIndex : assignmentSlot target ≠ indexSlot lastTarget := by
    simpa [assignmentSlot, indexSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := assignmentRegion) (rightRegion := indexRegion)
        (by norm_num [assignmentRegion]) (by norm_num [indexRegion])
        htarget hlastTarget
        (by norm_num [assignmentRegion, indexRegion])
  have hindex : assignmentSlot target ≠ indexSlot target := by
    simpa [assignmentSlot, indexSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := assignmentRegion) (rightRegion := indexRegion)
        (by norm_num [assignmentRegion]) (by norm_num [indexRegion])
        htarget htarget
        (by norm_num [assignmentRegion, indexRegion])
  have hcount : assignmentSlot target ≠ countSlot oldPauser := by
    simpa [assignmentSlot, countSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := assignmentRegion) (rightRegion := countRegion)
        (by norm_num [assignmentRegion]) (by norm_num [countRegion])
        htarget holdPauser
        (by norm_num [assignmentRegion, countRegion])
  rw [addLog_setMach_getStorVal,
    removalPost_getStorVal_other _ _ _ _ _ _ _ _ hmoved hlastIndex htail
      hlength hindex]
  exact foundKernelPost_assignment sevm base target 0 oldPauser oldCount hcount

/-! ## The removal tower is the state `pauseAfterSet` is entered from

`pauseAfterSetEntry_assignment` names a state and shows the assignment cell
is `0` there; it says nothing about whether that state is actually where
`pauseAfterSet` starts.  The substrate's two removal-walk theorems supply
that: `removeTarget_swapPop_toFinish_runCompiled` reaches `finishSetPauser`'s
entry, and `finishSetPauser_pauseAfterSet_runCompiled` crosses
`finishSetPauser`'s own body — the `PauserSet` emission — to
`pauseAfterSet`'s entry, gated on `hcontinuation`, the premise that picks out
a pause's continuation rather than a registration's. Composing the two turns
that chain into one machine-checked run. -/

/-- The removal tower plus the `PauserSet` record, entered as
`pauseAfterSet`'s own state on the pause's continuation.  This is the
composition `pauseAfterSetEntry_assignment` needs to be a statement about the
pause's actual boundary rather than about a state only this module named: it
chains `removeTarget_swapPop_toFinish_runCompiled`'s five writes to
`finishSetPauser_pauseAfterSet_runCompiled`'s crossing of `finishSetPauser`'s
body, with `newPauser` fixed at `0` throughout, which is what a pause's
clearing write means.

`previousPauser` and the staged memory image `imgFinish` are not among
`removeTarget_swapPop_toFinish_runCompiled`'s own premises — they belong to
`finishSetPauser`'s record and to the memory layout its body reads, so they
and the facts about them are supplied here as fresh premises rather than
re-derived from the removal span's own hypotheses. `pauseGas` plays the same
role for the gas split: `finishSetPauser_pauseAfterSet_runCompiled` fixes its
own body's cost at `1934` against an arbitrary entry gas, so `hpauseGas`
is the bridge that lets `finishGas` absorb it. -/
theorem removeTarget_pauseAfterSet_runCompiled
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
    (previousPauser : B256) (imgFinish : Bytes) (pauseGas : Nat)
    (hpauseGas : G + finishGas = pauseGas + 1934)
    (MLast : Mem)
    (hMLast : MLast =
      ((M.write (removedIndexWord * 32).toNat idx.toBytes).write
          (arrayLengthWord * 32).toNat len.toBytes).write
        (lastTargetWord * 32).toNat lastTarget.toBytes)
    (hreadsFinish : Mem.Reads MLast imgFinish)
    (htargetFinish : Bytes.toB256
      (imgFinish.sliceD (targetWord * 32).toNat 32 0) = target)
    (hpreviousFinish : Bytes.toB256
      (imgFinish.sliceD (previousPauserWord * 32).toNat 32 0) =
      previousPauser)
    (hnewFinish : Bytes.toB256
      (imgFinish.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuationFinish : Bytes.toB256
      (imgFinish.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hsizeFinish : 640 ≤ MLast.size) (halignFinish : MLast.size % 32 = 0)
    (hpause : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (((indexClearPost sevm (swapPopClearPost sevm base lastTarget idx len)
            target oldLength).addLog
          ⟨sevm.currentTarget,
            [pauserSetEvent, target, previousPauser, 0], []⟩).setMach
        ⟨stack, MLast, pauseGas⟩)
      pauseAfterSet post) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M,
        G + finishGas + 439 + lastExtCost + indexExtCost + lengthExtCost +
          holeCost + movedIndexCost + tailClearCost + lengthRestoreCost +
          indexClearCost⟩)
      removeTarget post := by
  refine removeTarget_swapPop_toFinish_runCompiled dp sevm base M img target
    lastTarget idx len oldLength stack hstack holeCurrent movedCurrent
    holeOriginal movedOriginal tailOriginal lengthOriginal indexOriginal
    holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost
    finishGas G hwf hreads htarget htargetValid hlastValid hlastNe
    hidxNonzero hidxBound hlenNonzero hlenBound hidxNeLen entrySize
    indexExtCost lengthExtCost lastExtCost hsize halign hentryLow
    hindexExtCost hlengthExtCost hlastExtCost hhole hmoved htail hindex
    hlength hholeOrig hmovedOrig htailOrig hindexOrig hlengthOrig hholeCost
    hmovedIndexCost htailClearCost hlengthRestoreCost hindexClearCost
    hwarmHole hwarmMoved hwarmTail hwarmIndex hwarmLength hsub hgasFinal
    hstatic post ?_
  subst hMLast
  rw [hpauseGas]
  exact finishSetPauser_pauseAfterSet_runCompiled dp sevm _ _ imgFinish
    target previousPauser 0 stack pauseGas post hstack hreadsFinish
    htargetFinish hpreviousFinish hnewFinish hcontinuationFinish hsizeFinish
    halignFinish hstatic hpause

/-! ## P4: a re-entering pause is refused

The lock is taken *before* `pause` yields control, so the target that receives
control is looking at a CircuitBreaker whose lock is already set.  This is the
half that gives that fact its meaning: entered from such a state, `pause`
cannot get past its own reentrancy guard.

Nothing below constrains the code at any address.  `sevm` is arbitrary — an
arbitrary caller, an arbitrary `currentTarget`, arbitrary calldata — and
`target` is an arbitrary address-shaped word.  The only premises are about the
calldata the re-entering caller supplies and about the lock cell itself; a
hostile callee discharges them exactly as a cooperative one does.  In
particular this says nothing about the pause completing: the published
callback-visible liveness counterexample stands. -/

/-- Frame-local gas of a refused re-entrant `pause`, from the endpoint's entry
to its `REVERT`.

`21` for `requireStaticArgs 1` and `33` for `canonicalAddressArg 0`; `3` for
the lock key push, `100` for the `TLOAD` and `3` for the `ISZERO`; `13` for the
zero arm of the lock branch — a zero arm pays no `JUMPDEST`, which is the whole
difference from the taken arm's `14`; `12` for the `.call` burn and `17` for
`reentrantCallError`'s `revSelectorCost` against empty memory. -/
def pauseReentrantGas : Nat := 202

set_option maxRecDepth 556 in
/-- A `pause` entered with the reentrancy lock already set takes the lock
guard's refusal arm and reverts with `ReentrantCall`'s own four-byte payload,
leaving storage, transient storage and the log list untouched. -/
theorem pause_body_runCompiledTo_error_of_locked
    (dp : DeployParams) (sevm : Sevm) (base : Devm) (target : B256) (G : Nat)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hlocked : base.getTransVal sevm.currentTarget lockKey ≠ 0) :
    ∃ post,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty, G + pauseReentrantGas⟩)
        pause (.error (.revert, post)) ∧
      post.output = customErrorData "ReentrantCall" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      (∀ a k, post.getTransVal a k = base.getTransVal a k) := by
  let errData := customErrorData "ReentrantCall"
  refine ⟨(base.setMach
      ⟨[], Mem.empty.write 0 errData.toB256.toBytes, G⟩).withOutput errData,
    ?_, rfl, rfl, ?_, ?_⟩
  · unfold pauseReentrantGas pause requireStaticArgs canonicalAddressArg arg
      cdl checkNonAddress pushAddressMask
    func_run (12) [0, ~~~(0 : B256), addressMask, 0]
    case h_val =>
      rw [hdataLength]
      decide +kernel
    case h_val =>
      rw [show (32 * 0 + 4 : B256) = 4 by decide +kernel, hdataTarget]
      exact hmask
    case h_arm =>
      func_run (1)
      set total := G + 202 with htotal
      have htload : Ninst.RunCompiled sevm
          (base.setMach ⟨[lockKey], Mem.empty, total - 57⟩) Ninst.tload
          (base.setMach
            ⟨[base.getTransVal sevm.currentTarget lockKey], Mem.empty,
              total - 157⟩) := by
        have h := runCompiled_tload_of (sevm := sevm)
          (pre := base.setMach ⟨[lockKey], Mem.empty, total - 57⟩)
          (key := lockKey)
          (value := base.getTransVal sevm.currentTarget lockKey)
          (stack := []) (G := total - 157) rfl rfl
          (by simp only [Devm.gasLeft_setMach, gasWarmAccess, htotal]; omega)
          (by simp)
        simpa only [Devm.memory_setMach, Devm.setMach_setMach] using h
      refine Func.RunCompiledTo.next htload ?_
      func_run (3) [0]
      case h_val =>
        simp [B256.eqCheck, hlocked]
      case h_body =>
        apply Func.runCompiledTo_revSelector (G := G)
        · simp [customErrorData, B256.length_toBytes]
        · exact Mem.wf_empty
        · exact Mem.reads_empty
        · rfl
        · simp only [Devm.gasLeft_setMach, revSelectorCost]
          rw [Devm.extCost_empty_word]
          norm_num [gVerylow, gBase, gMemory]
          omega
        · simp only [Devm.stack_setMach, List.length_nil]
          omega
  · intro a k
    rfl
  · intro a k
    rfl

/-- The same refusal at the deployed runtime's own entry: a re-entering call
that reaches the CircuitBreaker while the lock is held reverts with
`ReentrantCall`, having written nothing.

The premises are the two `pause` needs of any caller — a well-formed
`pause(address)` calldata frame and no attached value — plus the identity of
the CircuitBreaker's *own* code.  Nothing constrains the code at `target`, or
at any other address: `target` is an arbitrary address-shaped word and `sevm`
carries an arbitrary caller.  A re-entrant call that is malformed, or that
attaches value, still reverts; it just reverts at an earlier guard, which is
why those two premises are here rather than dropped. -/
theorem pause_runCompiledTo_error_of_locked
    (dp : DeployParams) (sevm : Sevm) (base : Devm) (target : B256) (G : Nat)
    (hdataLength : sevm.data.length = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "pause" [.address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hmask : addressMask &&& target = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hlocked : base.getTransVal sevm.currentTarget lockKey ≠ 0) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + pauseDispatchGas + pauseReentrantGas⟩)
        (runtime dp) (.error (.revert, post)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) ∧
      post.output = customErrorData "ReentrantCall" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      (∀ a k, post.getTransVal a k = base.getTransVal a k) := by
  obtain ⟨post, hbody, hout, hlogs, hstor, htrans⟩ :=
    pause_body_runCompiledTo_error_of_locked dp sevm base target G
      hdataLength hmask hdataTarget hlocked
  obtain ⟨hprog, hcompile⟩ :=
    pause_dispatch_runCompiledTo dp sevm base pauseReentrantGas G
      (.error (.revert, post)) hdataLength hvalue hselector hcodeAddress
      hcode hbody
  exact ⟨post, hprog, hcompile, hout, hlogs, hstor, htrans⟩

/-! ## P3: nothing moves between the boundary and the CALL

`pauseAfterSet` opens by loading the staged target, duplicating it and testing
`EXTCODESIZE`, and its live arm drops the duplicate, stages the
`pauseFor(uint256)` selector and the duration into memory, and pushes the
CALL's seven operands.  Twenty-one instructions, of which the only writes are
to memory: no `SSTORE` and no `TSTORE` stands between the boundary and the
moment the target receives control.

So P1 and P2 hold not merely at the `pauseAfterSet` entry but at the CALL
itself.  The span stops at the CALL's pre-state, which is the whole point:
what the callee does with control is exactly what these theorems decline to
say, and `Ninst.Run` at `Ninst.exec Xinst.call` embeds a complete child-frame
derivation, so no invariance across the CALL instruction could be true of an
arbitrary callee anyway. -/

theorem pauseCodeGuard_storInv : Line.Inv Devm.getStor pauseCodeGuard := by
  unfold pauseCodeGuard loadWord
  simp only [List.cons_append, List.nil_append]
  line_inv

theorem pauseCodeGuard_codeInv : Line.Inv Devm.getCode pauseCodeGuard := by
  unfold pauseCodeGuard loadWord
  simp only [List.cons_append, List.nil_append]
  line_inv

theorem pauseCodeGuard_transInv :
    Line.Inv Devm.transientStorage pauseCodeGuard := by
  unfold pauseCodeGuard loadWord
  simp only [List.cons_append, List.nil_append]
  line_inv

theorem pauseCallStaging_transInv :
    Line.Inv Devm.transientStorage pauseCallStaging := by
  unfold pauseCallStaging mstoreAt loadWord pushList
  simp only [List.map, List.cons_append, List.nil_append]
  line_inv

/-- **P3.**  Neither storage nor transient storage moves between the
`pauseAfterSet` entry and the external CALL.  The branch between the two named
spans is the code-size guard's own dispatch, which only pops its flag. -/
theorem pauseCallEntry_frame {sevm : Sevm}
    {entry guardPost branchPost callPre : Devm} {xs : List B256}
    (hguard : Line.Run sevm entry pauseCodeGuard guardPost)
    (hbranch : Devm.PopBurn xs guardPost branchPost)
    (hstaging : Line.Run sevm branchPost pauseCallStaging callPre) :
    Devm.getStor callPre = Devm.getStor entry ∧
      Devm.transientStorage callPre = Devm.transientStorage entry := by
  refine ⟨?_, ?_⟩
  · exact ((Line.of_inv Devm.getStor pauseCodeGuard_storInv hguard).trans
      ((PopBurn.Inv.inv hbranch).trans
        (Line.of_inv Devm.getStor pauseCallStaging_storInv hstaging))).symm
  · exact ((Line.of_inv Devm.transientStorage pauseCodeGuard_transInv
      hguard).trans ((PopBurn.Inv.inv hbranch).trans
        (Line.of_inv Devm.transientStorage pauseCallStaging_transInv
          hstaging))).symm

/-- **P1 and P2 at the CALL itself.**  Whatever the target's code is, at the
instant it receives control the CircuitBreaker's own state says the paused
target has no pauser and the reentrancy lock is held.

`entry` is the `pauseAfterSet` entry state, whose two cells
`pauseAfterSetEntry_assignment` and the `pauseLockPost`/`pauseKernelBase` lock
results supply; this carries both across the guard and the call staging to the
CALL's pre-state.  Nothing constrains the code at `target`: the run hypotheses
are about the CircuitBreaker's own frame, and a hostile callee is on the far
side of the CALL this span stops at. -/
theorem pauseCallEntry_assignment_and_lock {sevm : Sevm}
    {entry guardPost branchPost callPre : Devm} {xs : List B256}
    {target : B256}
    (hguard : Line.Run sevm entry pauseCodeGuard guardPost)
    (hbranch : Devm.PopBurn xs guardPost branchPost)
    (hstaging : Line.Run sevm branchPost pauseCallStaging callPre)
    (hassignment : entry.getStorVal sevm.currentTarget
      (assignmentSlot target) = 0)
    (hlock : entry.getTransVal sevm.currentTarget lockKey = 1) :
    callPre.getStorVal sevm.currentTarget (assignmentSlot target) = 0 ∧
      callPre.getTransVal sevm.currentTarget lockKey = 1 := by
  obtain ⟨hstor, htrans⟩ := pauseCallEntry_frame hguard hbranch hstaging
  refine ⟨?_, ?_⟩
  · rw [show callPre.getStorVal sevm.currentTarget (assignmentSlot target) =
      (Devm.getStor callPre sevm.currentTarget).get (assignmentSlot target)
        from rfl, hstor]
    exact hassignment
  · rw [show callPre.getTransVal sevm.currentTarget lockKey =
      (callPre.transientStorage.getD sevm.currentTarget Stor.empty).get lockKey
        from rfl, htrans]
    exact hlock

end Blanc.LidoCircuitBreaker
