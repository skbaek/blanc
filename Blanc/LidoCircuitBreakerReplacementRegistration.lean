import Blanc.LidoCircuitBreakerRegistrySubstrate

/-!
Replacement chronology for the Lido CircuitBreaker.

The target is already registered to a nonzero previous pauser and the new pauser
is nonzero, so `setPauser` replaces the assignment, decrements the old pauser's
count and increments the new pauser's — the three-write found-nonzero Registry
walk of `setPauserKernel_foundNonzero_finishSetPauser_runCompiled`.

`registerAfterSet` then branches on the old pauser's *remaining* count, and both
arms are carried here, each from its `registerAfterSet` walk up to the settled
effects of a direct `registerPauser` message:

* the **retained** arm, where the remaining count is nonzero: no expiry moves
  but the new pauser's, and exactly two records are emitted;
* the **old-last** arm, where it is zero: the old pauser's heartbeat expiry is
  cleared and a zero-payload `HeartbeatUpdated(oldPauser)` is emitted before the
  shared nonzero-new-pauser suffix runs, for three records in all.

Every statement leaves `oldPauser` and `newPauser` as unrelated binders and
reads each later value out of the poststate of the write before it, so the
same-pauser replacement is an instantiation rather than a fourth chronology.
It instantiates the **retained** arm: with `oldPauser = newPauser` the two count
writes hit one slot, so what `registerAfterSet` reads back is `1 + (oldCount -
1)`, and the arm on the old-last side is the one a same-pauser call does not
reach.  A new pauser that already holds other targets is likewise just a
different entry count, in either arm.

What is *not* here is the bridge to the Registry model: these theorems fix the
three writes operationally and by cost, but do not yet state that the resulting
storage is `applyRegistryWrites` of the found-nonzero source trace.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst


/-! ## Model-side replacement chronology -/

/-- The found-target/nonzero-pauser model branch derives the exact replacement
chronology and its refined Registry witness: three writes, in the order the
generated kernel performs them, and the post-state entry list with the target's
recorded pauser replaced in place.

The old and new pausers are not assumed distinct.  When they coincide the third
write lands on the slot the second one decremented, which is exactly why the
model's new-count value carries the `if oldPauser = newPauser` correction. -/
theorem foundNonzeroReplacement_sourceTrace_witness
    {s : Stor} {entries : List Entry} {target newPauser oldPauser : B256}
    {index : Nat}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = some (index, oldPauser)) :
    ∃ trace : SetPauserSourceTrace,
      setPauserSourceTrace entries target newPauser = some trace ∧
      trace.postEntries = setEntryAt index (target, newPauser) entries ∧
      trace.writes =
        [(assignmentSlot target, newPauser),
         (countSlot oldPauser,
           Nat.toB256 (assignmentCount entries oldPauser - 1)),
         (countSlot newPauser,
           Nat.toB256
             ((assignmentCount entries newPauser -
               (if oldPauser = newPauser then 1 else 0)) + 1))] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites s trace.writes))
        trace.postEntries := by
  have hpost : setPauser entries target newPauser =
      some (setEntryAt index (target, newPauser) entries) := by
    simp [setPauser, htarget.1, hfind, hnew.1]
  have htrace : setPauserSourceTrace entries target newPauser =
      some {
        postEntries := setEntryAt index (target, newPauser) entries
        writes :=
          [(assignmentSlot target, newPauser),
           (countSlot oldPauser,
             Nat.toB256 (assignmentCount entries oldPauser - 1)),
           (countSlot newPauser,
             Nat.toB256
               ((assignmentCount entries newPauser -
                 (if oldPauser = newPauser then 1 else 0)) + 1))] } := by
    simp [setPauserSourceTrace, hpost,
      setPauserSourceWrites_found_nonzero entries target newPauser index
        oldPauser htarget.1 hfind hnew.1]
  refine ⟨_, htrace, rfl, rfl, ?_⟩
  exact hw.applyFoundNonzeroWrites htarget hnew hfind


set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Exact `registerAfterSet` walk for a replacement that leaves the previous
pauser holding **no** further assignment: the previous pauser is nonzero, its
remaining count is zero and the new pauser is nonzero.  The walk clears the old
pauser's heartbeat expiry, emits `HeartbeatUpdated(oldPauser)` with a zero
payload, then computes and stores the new pauser's checked heartbeat expiry and
emits `HeartbeatUpdated(newPauser)`.

Both restrictions are premises and both are named: `hcount` is the old-last
restriction and `hnewNonzero` is the replacement restriction.  This is the
nonzero-new-pauser counterpart of `registerAfterSet_oldLastZero_runCompiled`,
and it composes the same substrate prefix — 1567 gas plus the expiry-clear value
cost — with the substrate's shared suffix — 3569 gas plus the expiry-store value
cost — for `5136 + clearCost + storeCost` in total.

The new pauser's interval read, current expiry and original expiry are stated
against the **poststate of the old-pauser expiry clear**, exactly as the
found-nonzero kernel states its new count against the poststate of the old-count
decrement.  So no disjointness between the two expiry slots, or between the old
expiry slot and the interval slot, is assumed anywhere: the same-pauser
replacement instantiates this as readily as the distinct one. -/
theorem registerAfterSet_oldLastNonzero_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (oldPauser oldExpiry oldExpiryOriginal newPauser timestamp interval
      expiry currentExpiry expiryOriginal : B256)
    (stack : List B256) (clearCost storeCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (holdNonzero : oldPauser ≠ 0)
    (hnewNonzero : newPauser ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget (countSlot oldPauser) = 0)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (holdExpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmOldExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (temporalSstorePost sevm base
      (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hexpiry : (temporalSstorePost sevm base
      (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 5136 + clearCost + storeCost⟩)
      registerAfterSet
      (((temporalSstorePost sevm
          (temporalSloadBase sevm
            ((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
              ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
                (0 : B256).toBytes⟩)
            heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨stack, (M.write 0 (0 : B256).toBytes).write 0 expiry.toBytes, G⟩) := by
  have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
      (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
  have accessedStorageKeys_addLog (d : Devm) (l : Log) :
      (d.addLog l).accessedStorageKeys = d.accessedStorageKeys := rfl
  have hsize0 : (M.write 0 (0 : B256).toBytes).size = M.size :=
    Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show 0 + 32 ≤ M.size by omega))
  have hnew0 : Bytes.toB256
      ((Bytes.writeAt img 0 (0 : B256).toBytes).sliceD
        (newPauserWord * 32).toNat 32 0) = newPauser := by
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      simp only [B256.length_toBytes]
      decide)]
    exact hnew
  have hintervalCold0 : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      ((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
          (0 : B256).toBytes⟩).accessedStorageKeys := by
    rw [accessedStorageKeys_addLog, temporalSstorePost_accessedStorageKeys]
    exact hintervalCold
  have hwarmNewExpiry0 : (sevm.currentTarget, expirySlot newPauser) ∈
      ((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
          (0 : B256).toBytes⟩).accessedStorageKeys := by
    rw [accessedStorageKeys_addLog, temporalSstorePost_accessedStorageKeys]
    exact hwarmNewExpiry
  have htail := registerAfterSet_nonzeroNewPauserTail_runCompiled fs sevm
    ((temporalSstorePost sevm base (expirySlot oldPauser) 0).addLog
      ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
        (0 : B256).toBytes⟩)
    (M.write 0 (0 : B256).toBytes) (Bytes.writeAt img 0 (0 : B256).toBytes)
    newPauser timestamp interval expiry currentExpiry expiryOriginal stack
    storeCost G hstack (Mem.Wf.write hwf _ _) (Mem.Reads.write hwf hreads 0 _)
    hnew0 hnewNonzero (by omega) (by rw [hsize0]; exact halign) htime
    (by rw [getStorVal_addLog]; exact hinterval) hintervalCold0
    (by rw [getStorVal_addLog]; exact hexpiry) hexpiryOrig hwarmNewExpiry0
    hstoreCost hgasStipend hstatic hextension
  have h := registerAfterSet_oldLast_newPauserTail_runCompiled fs sevm base M
    img oldPauser oldExpiry oldExpiryOriginal stack clearCost
    (G + 3569 + storeCost) _ hstack hwf hreads hprevious holdNonzero hcount
    hwarmCount holdExpiry holdExpiryOrig hwarmOldExpiry hclearCost (by omega)
    hstatic hsize halign htail
  have hg : G + 3569 + storeCost + 1567 + clearCost =
      G + 5136 + clearCost + storeCost := by omega
  rw [hg] at h
  exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The same walk lifted through `finishSetPauser`: the `PauserSet(target,
oldPauser, newPauser)` record is emitted first, then the old-last replacement
`registerAfterSet` arm runs.  1935 gas of shared `finishSetPauser` glue above
`registerAfterSet_oldLastNonzero_runCompiled`, for `7071 + clearCost +
storeCost` in total.

Both restrictions of the underlying arm survive verbatim as `hcount` and
`hnewNonzero`; the emitted `PauserSet` record is storage- and
accessed-key-neutral, so every entry-state premise is still stated against
`base`. -/
theorem finishSetPauser_oldLastNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldPauser oldExpiry oldExpiryOriginal newPauser timestamp interval
      expiry currentExpiry expiryOriginal : B256)
    (stack : List B256) (clearCost storeCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (holdNonzero : oldPauser ≠ 0)
    (hnewNonzero : newPauser ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget (countSlot oldPauser) = 0)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot oldPauser) = oldExpiry)
    (holdExpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmOldExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      base.accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (temporalSstorePost sevm base
      (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hexpiry : (temporalSstorePost sevm base
      (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G + 7071 + clearCost + storeCost⟩)
      finishSetPauser
      (((temporalSstorePost sevm
          (temporalSloadBase sevm
            ((temporalSstorePost sevm
              (base.addLog ⟨sevm.currentTarget,
                [pauserSetEvent, target, oldPauser, newPauser], []⟩)
              (expirySlot oldPauser) 0).addLog
              ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
                (0 : B256).toBytes⟩)
            heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨stack, (M.write 0 (0 : B256).toBytes).write 0 expiry.toBytes, G⟩) := by
  have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
      (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
  have accessedStorageKeys_addLog (d : Devm) (l : Log) :
      (d.addLog l).accessedStorageKeys = d.accessedStorageKeys := rfl
  have getStorVal_storePost_addLog (d : Devm) (l : Log) (k v : B256)
      (a : Adr) (k' : B256) :
      (temporalSstorePost sevm (d.addLog l) k v).getStorVal a k' =
        (temporalSstorePost sevm d k v).getStorVal a k' := rfl
  have hregister := registerAfterSet_oldLastNonzero_runCompiled
    ((runtime dp).main :: (runtime dp).aux) sevm
    (base.addLog ⟨sevm.currentTarget,
      [pauserSetEvent, target, oldPauser, newPauser], []⟩)
    M img oldPauser oldExpiry oldExpiryOriginal newPauser timestamp interval
    expiry currentExpiry expiryOriginal stack clearCost storeCost G hstack hwf
    hreads hprevious hnew holdNonzero hnewNonzero
    (by rw [getStorVal_addLog]; exact hcount)
    (by rw [accessedStorageKeys_addLog]; exact hwarmCount)
    (by rw [getStorVal_addLog]; exact holdExpiry)
    holdExpiryOrig
    (by rw [accessedStorageKeys_addLog]; exact hwarmOldExpiry)
    hclearCost htime
    (by rw [getStorVal_storePost_addLog]; exact hinterval)
    (by rw [accessedStorageKeys_addLog]; exact hintervalCold)
    (by rw [getStorVal_storePost_addLog]; exact hexpiry)
    hexpiryOrig
    (by rw [accessedStorageKeys_addLog]; exact hwarmNewExpiry)
    hstoreCost hgasStipend hstatic hsize halign hextension
  have h := finishSetPauser_registerAfterSet_runCompiled dp sevm base M img
    target oldPauser newPauser stack (G + 5136 + clearCost + storeCost) _
    hstack hreads htarget hprevious hnew hcontinuation hsize halign hstatic
    hregister
  have hg : G + 5136 + clearCost + storeCost + 1935 =
      G + 7071 + clearCost + storeCost := by omega
  rw [hg] at h
  exact h

/-! ## Retained replacement -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Generic **retained** arm of `registerAfterSet`: the previous pauser is
nonzero and its remaining assignment count is nonzero, so the walk touches no
storage at all before reaching the shared new-pauser suffix, which is taken as a
hypothesis.  Generic in that suffix, exactly as the old-last prefix in the
substrate is.

Glue cost 150 gas above the suffix: 22 for the outer previous-pauser load, its
`iszero` and the untaken branch, 12 for `previousCountKey`, 100 for the warm
count `SLOAD`, 3 for its `iszero` and 13 for the untaken inner branch.  The
count `SLOAD` is charged warm, which `hwarmCount` states as a premise exactly as
the old-last sibling does. -/
private theorem registerAfterSet_retained_newPauserTail_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (oldPauser remaining : B256)
    (stack : List B256) (G : Nat) (post : Devm)
    (hstack : stack.length ≤ 1)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (holdNonzero : oldPauser ≠ 0)
    (hremaining : remaining ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (htail : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G⟩)
      (loadWord newPauserWord +++ Ninst.iszero :::
        (Func.stop <?>
          (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++
            Ninst.sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 150⟩)
      registerAfterSet post := by
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hpreviousMemory :
      (M.read (previousPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hpreviousCovered)]
  have hpreviousValue :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = oldPauser := by
    rw [Mem.Reads.read hreads]
    exact hprevious
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
      (base.setMach ⟨countSlot oldPauser :: stack, M, G + 116⟩)
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
      post := by
    func_run (3) [0]
    all_goals try ((try simp only [Devm.stack_setMach, List.length_cons]); omega)
    case h_val =>
      rw [Devm.getStorVal_setMach, hcount]
      simp [B256.eqCheck, hremaining]
    case h_arm => exact htail
  have holdTail : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 128⟩) oldBranch post :=
    previousCountKey_prepend_runCompiled hpreviousValue
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
    have hg : G + 150 - 22 = G + 128 := by omega
    rw [hg]
    change Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 128⟩) oldBranch post
    exact holdTail

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Exact `registerAfterSet` walk for a replacement that leaves the previous
pauser holding a **further** assignment: the previous pauser is nonzero, its
remaining count is nonzero and the new pauser is nonzero.  The walk reads the
old count, takes the retained arm without touching any expiry slot, then
computes and stores the new pauser's checked heartbeat expiry and emits
`HeartbeatUpdated(newPauser)`.

Both restrictions are premises and both are named: `hremaining` is the retained
restriction and `hnewNonzero` is the replacement restriction.  This is the
retained counterpart of `registerAfterSet_oldLastNonzero_runCompiled`, and it
composes the retained prefix — 150 gas, no writes — with the substrate's shared
suffix — 3569 gas plus the expiry-store value cost — for `3719 + storeCost` in
total.

Because the retained arm writes nothing before the suffix, every entry-state
premise is stated against `base` itself; no state tower separates the old-count
read from the new pauser's interval read, current expiry and original expiry.
`oldPauser` and `newPauser` are unrelated binders and no slot is assumed
disjoint from any other, so the same-pauser replacement instantiates this as
readily as the distinct one. -/
theorem registerAfterSet_retainedNonzero_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (oldPauser remaining newPauser timestamp interval expiry currentExpiry
      expiryOriginal : B256)
    (stack : List B256) (storeCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (holdNonzero : oldPauser ≠ 0)
    (hnewNonzero : newPauser ≠ 0)
    (hremaining : remaining ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M, G + 3719 + storeCost⟩)
      registerAfterSet
      (((temporalSstorePost sevm
          (temporalSloadBase sevm base heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨stack, M.write 0 expiry.toBytes, G⟩) := by
  have htail := registerAfterSet_nonzeroNewPauserTail_runCompiled fs sevm base
    M img newPauser timestamp interval expiry currentExpiry expiryOriginal
    stack storeCost G hstack hwf hreads hnew hnewNonzero hsize halign htime
    hinterval hintervalCold hexpiry hexpiryOrig hwarmNewExpiry hstoreCost
    hgasStipend hstatic hextension
  have h := registerAfterSet_retained_newPauserTail_runCompiled fs sevm base M
    img oldPauser remaining stack (G + 3569 + storeCost) _ hstack hreads
    hprevious holdNonzero hremaining hcount hwarmCount hsize halign htail
  have hg : G + 3569 + storeCost + 150 = G + 3719 + storeCost := by omega
  rw [hg] at h
  exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The retained replacement walk lifted through `finishSetPauser`: the
`PauserSet(target, oldPauser, newPauser)` record is emitted first, then the
retained `registerAfterSet` arm runs.  1935 gas of shared `finishSetPauser` glue
above `registerAfterSet_retainedNonzero_runCompiled`, for `5654 + storeCost` in
total.

Both restrictions of the underlying arm survive verbatim as `hremaining` and
`hnewNonzero`; the emitted `PauserSet` record is storage- and
accessed-key-neutral, so every entry-state premise is still stated against
`base`. -/
theorem finishSetPauser_retainedNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldPauser remaining newPauser timestamp interval expiry
      currentExpiry expiryOriginal : B256)
    (stack : List B256) (storeCost G : Nat)
    (hstack : stack.length ≤ 1)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (holdNonzero : oldPauser ≠ 0)
    (hnewNonzero : newPauser ≠ 0)
    (hremaining : remaining ≠ 0)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot oldPauser) = remaining)
    (hwarmCount : (sevm.currentTarget, countSlot oldPauser) ∈
      base.accessedStorageKeys)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨stack, M, G + 5654 + storeCost⟩)
      finishSetPauser
      (((temporalSstorePost sevm
          (temporalSloadBase sevm
            (base.addLog ⟨sevm.currentTarget,
              [pauserSetEvent, target, oldPauser, newPauser], []⟩)
            heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨stack, M.write 0 expiry.toBytes, G⟩) := by
  have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
      (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
  have accessedStorageKeys_addLog (d : Devm) (l : Log) :
      (d.addLog l).accessedStorageKeys = d.accessedStorageKeys := rfl
  have hregister := registerAfterSet_retainedNonzero_runCompiled
    ((runtime dp).main :: (runtime dp).aux) sevm
    (base.addLog ⟨sevm.currentTarget,
      [pauserSetEvent, target, oldPauser, newPauser], []⟩)
    M img oldPauser remaining newPauser timestamp interval expiry
    currentExpiry expiryOriginal stack storeCost G hstack hwf hreads hprevious
    hnew holdNonzero hnewNonzero hremaining
    (by rw [getStorVal_addLog]; exact hcount)
    (by rw [accessedStorageKeys_addLog]; exact hwarmCount)
    htime
    (by rw [getStorVal_addLog]; exact hinterval)
    (by rw [accessedStorageKeys_addLog]; exact hintervalCold)
    (by rw [getStorVal_addLog]; exact hexpiry)
    hexpiryOrig
    (by rw [accessedStorageKeys_addLog]; exact hwarmNewExpiry)
    hstoreCost hgasStipend hstatic hsize halign hextension
  have h := finishSetPauser_registerAfterSet_runCompiled dp sevm base M img
    target oldPauser newPauser stack (G + 3719 + storeCost) _
    hstack hreads htarget hprevious hnew hcontinuation hsize halign hstatic
    hregister
  have hg : G + 3719 + storeCost + 1935 = G + 5654 + storeCost := by omega
  rw [hg] at h
  exact h

/-! ## Registry walks -/

/-- State reached by the complete found-nonzero Registry walk: the target's
assignment has been replaced by `newPauser`, the old pauser's count has been
decremented and the new pauser's count has been incremented to `nextCount`.
This is a six-layer `temporalSstorePost`/`temporalSloadBase` tower on top of
`foundKernelPost`; keep it folded under this name and never cross it by `exact`,
`change` or `rfl`.  See README.md, *Proof-performance conventions*.

`oldPauser` and `newPauser` are unrelated binders here, so the count slot the
last write lands on may be the very slot the middle write decremented — the
same-pauser replacement — and nothing in this definition assumes otherwise. -/
def foundNonzeroKernelPost (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount nextCount : B256) : Devm :=
  temporalSstorePost sevm
    (temporalSloadBase sevm
      (foundKernelPost sevm base target newPauser oldPauser oldCount)
      (countSlot newPauser))
    (countSlot newPauser) nextCount

/-- Exact `setPauserKernel` reserve for a retained replacement: the shared
found-nonzero Registry prefix, the new pauser's count read and write, and the
5654 gas plus expiry-store value cost of the retained `finishSetPauser` arm. -/
def replacementRetainedSetPauserKernelGas (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount : B256)
    (assignmentCost countCost newCountCost storeCost : Nat) : Nat :=
  5654 + storeCost +
    (64 + temporalSloadCost sevm
        (foundKernelPost sevm base target newPauser oldPauser oldCount)
        (countSlot newPauser) + newCountCost) +
    foundSetPauserKernelPrefixGas sevm base target newPauser oldPauser
      assignmentCost countCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Complete generated-kernel walk for a **retained** replacement: the target is
recorded to a nonzero `oldPauser`, the new pauser is nonzero, and the old
pauser's count after the decrement is still nonzero, so `registerAfterSet` moves
no expiry but the new pauser's.

The three Registry writes are the substrate's; the retained restriction is
`hremaining` together with `hremainingCount`, which reads the old pauser's count
*out of the walk's own poststate* rather than out of `base`.  That is what makes
the statement carry the same-pauser replacement: when `oldPauser = newPauser` the
slot named by `hremainingCount` is the slot the increment just wrote, and
`remaining` is then `nextCount`; when the two differ it is the decremented
`oldCount - 1`.  No disjointness between the count slots, or between either
count slot and the expiry or interval slots, is assumed anywhere. -/
theorem setPauserKernel_retainedNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target newPauser oldPauser oldCount newCount nextCount remaining
      timestamp interval expiry currentExpiry expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost storeCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
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
    (hremaining : remaining ≠ 0)
    (hremainingCount : (foundNonzeroKernelPost sevm base target newPauser
      oldPauser oldCount nextCount).getStorVal sevm.currentTarget
        (countSlot oldPauser) = remaining)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hexpiry : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M,
        G + replacementRetainedSetPauserKernelGas sevm base target newPauser
          oldPauser oldCount assignmentCost countCost newCountCost storeCost⟩)
      setPauserKernel
      (((temporalSstorePost sevm
          (temporalSloadBase sevm
            ((foundNonzeroKernelPost sevm base target newPauser oldPauser
                oldCount nextCount).addLog
              ⟨sevm.currentTarget,
                [pauserSetEvent, target, oldPauser, newPauser], []⟩)
            heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨[], (M.write (previousPauserWord * 32).toNat oldPauser.toBytes).write
          0 expiry.toBytes, G⟩) := by
  have hcovered : (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    rw [hsize]
    decide
  have hsize' :
      (M.write (previousPauserWord * 32).toNat oldPauser.toBytes).size =
        640 := by
    rw [Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using hcovered)]
    exact hsize
  have htarget' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (targetWord * 32).toNat 32 0) = target := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (newPauserWord * 32).toNat 32 0) =
      newPauser := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hcontinuation' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (continuationWord * 32).toNat 32 0) =
      0 := by
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      simp only [B256.length_toBytes]
      decide)]
    exact hcontinuation
  have hprevious' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      oldPauser := by
    have hslice := Bytes.sliceD_writeAt img oldPauser.toBytes
      (previousPauserWord * 32).toNat
    rw [B256.length_toBytes] at hslice
    rw [hslice]
    exact B256.toB256_toBytes oldPauser
  have hwarmOldCount : (sevm.currentTarget, countSlot oldPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys := by
    simp only [foundNonzeroKernelPost, temporalSstorePost_accessedStorageKeys]
    refine temporalSloadBase_preserves_warm _ _ _ _ ?_
    simp only [foundKernelPost, temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_warm _ _ _
  have hfinish := finishSetPauser_retainedNonzero_runCompiled dp sevm
    (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
      nextCount)
    (M.write (previousPauserWord * 32).toNat oldPauser.toBytes)
    (Bytes.writeAt img (previousPauserWord * 32).toNat oldPauser.toBytes)
    target oldPauser remaining newPauser timestamp interval expiry
    currentExpiry expiryOriginal [] storeCost G (by simp)
    (Mem.Wf.write hwf _ _) (Mem.Reads.write hwf hreads _ _) htarget'
    hprevious' hnew' hcontinuation' holdValid.1 hnewNonzero hremaining
    hremainingCount hwarmOldCount htime hinterval hintervalCold hexpiry
    hexpiryOrig hwarmNewExpiry hstoreCost hgasStipend hstatic
    (by omega) (by rw [hsize']) hextension
  dsimp only [foundNonzeroKernelPost] at hfinish
  have hkernel := setPauserKernel_foundNonzero_finishSetPauser_runCompiled dp
    sevm base M img _ target newPauser oldPauser oldCount newCount nextCount
    assignmentOriginal countOriginal newCountOriginal assignmentCost countCost
    newCountCost (G + 5654 + storeCost) hwf hreads htarget hnew htargetValid
    holdValid hnewNonzero hsize hassignment hassignmentOrig hassignmentCost
    hcount hcountOrig hcountCost hnewCount hnewCountOrig hnewCountNext
    hnewCountCost (by omega) hstatic hfinish
  have hg : G + replacementRetainedSetPauserKernelGas sevm base target
        newPauser oldPauser oldCount assignmentCost countCost newCountCost
        storeCost =
      G + 5654 + storeCost +
        (64 + temporalSloadCost sevm
          (foundKernelPost sevm base target newPauser oldPauser oldCount)
          (countSlot newPauser) + newCountCost) +
        foundSetPauserKernelPrefixGas sevm base target newPauser oldPauser
          assignmentCost countCost := by
    dsimp only [replacementRetainedSetPauserKernelGas]
    omega
  rw [hg]
  exact hkernel

/-! ## Replacement public boundary -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- The four scratch writes `registerPauser`'s body performs before entering
the kernel: the two decoded arguments and the two zero words.  The staging is
chronology-independent, so the kernel run is taken as a hypothesis.

This duplicates the private staging walk of
`Blanc/LidoCircuitBreakerUnregisterRegistration.lean`; the two should collapse
into one substrate declaration once no chronology module is being edited
concurrently. -/
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
  -- 46.4 s in the sibling module (measured); ordered `case h_ext` blocks
  -- brought the same proof to 5.1 s.
  case h_ext => exact Devm.extCost_of_size (n := 0) rfl (by decide +kernel)
  case h_ext =>
    exact Devm.extCost_of_size (n := 544) (hM1Size _) (by decide +kernel)
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

/-- Exact production-body reserve for a retained replacement. -/
def replacementRetainedRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount : B256)
    (assignmentCost countCost newCountCost storeCost : Nat) : Nat :=
  221 + replacementRetainedSetPauserKernelGas sevm base target newPauser
    oldPauser oldCount assignmentCost countCost newCountCost storeCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact successful production body for a **retained** replacement: an
admin-authorised `registerPauser(target, newPauser)` on a target already
recorded to a nonzero `oldPauser`, with a nonzero `newPauser` and a nonzero
remaining count for the old pauser.

The two records the call emits are exactly `PauserSet(target, oldPauser,
newPauser)` and `HeartbeatUpdated(newPauser)`; no `HeartbeatUpdated(oldPauser)`
appears, which is the observable signature that separates this partition from
the old-last one. -/
theorem registerPauser_body_retainedNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount newCount nextCount remaining
      timestamp interval expiry currentExpiry expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost storeCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = newPauser)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (holdValid : nonzeroCanonicalAddress oldPauser)
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
    (hremaining : remaining ≠ 0)
    (hremainingCount : (foundNonzeroKernelPost sevm base target newPauser
      oldPauser oldCount nextCount).getStorVal sevm.currentTarget
        (countSlot oldPauser) = remaining)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hexpiry : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + replacementRetainedRegisterBodyGas sevm base target newPauser
            oldPauser oldCount assignmentCost countCost newCountCost
            storeCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, oldPauser, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  rcases registerMemory_spec target newPauser with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      _hpreviousRead, hcontinuationRead⟩
  have hkernel := setPauserKernel_retainedNonzero_runCompiled dp sevm base
    (registerMemory target newPauser) (registerImage target newPauser)
    target newPauser oldPauser oldCount newCount nextCount remaining timestamp
    interval expiry currentExpiry expiryOriginal assignmentOriginal
    countOriginal newCountOriginal assignmentCost countCost newCountCost
    storeCost G hwf hreads htargetRead hnewRead hcontinuationRead htargetValid
    holdValid hnewValid.1 hsize hassignment hassignmentOrig hassignmentCost
    hcount hcountOrig hcountCost hnewCount hnewCountOrig hnewCountNext
    hnewCountCost hremaining hremainingCount htime hinterval hintervalCold
    hexpiry hexpiryOrig hwarmNewExpiry hstoreCost hgasStipend hstatic
    hextension
  have hstage := registerPauser_stageArgs_runCompiled dp sevm base target
    newPauser
    (G + replacementRetainedSetPauserKernelGas sevm base target newPauser
      oldPauser oldCount assignmentCost countCost newCountCost storeCost)
    _ hargTarget hargNew hkernel
  have hbody : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty,
        G + replacementRetainedRegisterBodyGas sevm base target newPauser
          oldPauser oldCount assignmentCost countCost newCountCost storeCost⟩)
      (registerPauser dp)
      (((temporalSstorePost sevm
          (temporalSloadBase sevm
            ((foundNonzeroKernelPost sevm base target newPauser oldPauser
                oldCount nextCount).addLog
              ⟨sevm.currentTarget,
                [pauserSetEvent, target, oldPauser, newPauser], []⟩)
            heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨[], ((registerMemory target newPauser).write
          (previousPauserWord * 32).toNat oldPauser.toBytes).write
          0 expiry.toBytes, G⟩) := by
    have htargetMask := canonicalAddress_mask_zero htargetValid.2
    have hnewMask := canonicalAddress_mask_zero hnewValid.2
    unfold registerPauser requireStaticArgs canonicalAddressArg onlyAdmin arg
      cdl checkNonAddress pushAddressMask pushDeployWord
    func_run (24) [0, ~~~(0 : B256), addressMask, 0,
      ~~~(0 : B256), addressMask, 0, 1]
    all_goals try { rw [hargTarget]; exact htargetMask }
    all_goals try { rw [hargNew]; exact hnewMask }
    all_goals try { simp [hadmin, B256.eqCheck] }
    all_goals first
      | (simp only [Devm.gasLeft_setMach, replacementRetainedRegisterBodyGas]
         norm_num [gBase, gVerylow, gHigh, gMid, gJumpdest]
         omega)
      | skip
    case h_arm =>
      simp only [replacementRetainedRegisterBodyGas]
      have hg : G + (221 + replacementRetainedSetPauserKernelGas sevm base
            target newPauser oldPauser oldCount assignmentCost countCost
            newCountCost storeCost) - 109 =
          G + replacementRetainedSetPauserKernelGas sevm base target newPauser
            oldPauser oldCount assignmentCost countCost newCountCost
            storeCost + 112 := by
        omega
      rw [hg]
      simpa only [arg, cdl] using hstage
  refine ⟨_, hbody, rfl, ?_, ?_⟩
  · have getStorVal_setMach (d : Devm) (mach : Mach) (a : Adr) (k : B256) :
        (d.setMach mach).getStorVal a k = d.getStorVal a k := rfl
    have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
        (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
    rw [getStorVal_setMach, getStorVal_addLog, temporalSstorePost_self]
  · have logs_setMach (d : Devm) (mach : Mach) :
        (d.setMach mach).logs = d.logs := rfl
    have logs_addLog (d : Devm) (l : Log) :
        (d.addLog l).logs = d.logs ++ [l] := rfl
    have hkernelLogs : (foundNonzeroKernelPost sevm base target newPauser
        oldPauser oldCount nextCount).logs = base.logs := by
      simp only [foundNonzeroKernelPost]
      rw [temporalSstorePost_logs, temporalSloadBase_logs]
      simp only [foundKernelPost]
      rw [temporalSstorePost_logs, temporalSloadBase_logs]
      simp only [assignmentPost]
      rw [temporalSstorePost_logs]
      simp only [assignmentBase]
      rw [temporalSloadBase_logs]
    rw [logs_setMach, logs_addLog, temporalSstorePost_logs,
      temporalSloadBase_logs, logs_addLog, hkernelLogs, List.append_assoc]
    rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-runtime success for a **retained** replacement: the
dispatcher's own reserve above `registerPauser_body_retainedNonzero_runCompiled`,
with the same effects. -/
theorem registerPauser_runCompiledTo_retainedNonzero
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount newCount nextCount remaining
      timestamp interval expiry currentExpiry expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost storeCost G : Nat)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = newPauser)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (holdValid : nonzeroCanonicalAddress oldPauser)
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
    (hremaining : remaining ≠ 0)
    (hremainingCount : (foundNonzeroKernelPost sevm base target newPauser
      oldPauser oldCount nextCount).getStorVal sevm.currentTarget
        (countSlot oldPauser) = remaining)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hexpiry : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            replacementRetainedRegisterBodyGas sevm base target newPauser
              oldPauser oldCount assignmentCost countCost newCountCost
              storeCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, oldPauser, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_retainedNonzero_runCompiled dp sevm base target
      newPauser oldPauser oldCount newCount nextCount remaining timestamp
      interval expiry currentExpiry expiryOriginal assignmentOriginal
      countOriginal newCountOriginal assignmentCost countCost newCountCost
      storeCost G hbodyData hadmin hargTarget hargNew htargetValid hnewValid
      holdValid hassignment hassignmentOrig hassignmentCost hcount hcountOrig
      hcountCost hnewCount hnewCountOrig hnewCountNext hnewCountCost
      hremaining hremainingCount htime hinterval hintervalCold hexpiry
      hexpiryOrig hwarmNewExpiry hstoreCost hgasStipend hstatic hextension with
    ⟨post, hbody, hgas, hstore, hlogs⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (replacementRetainedRegisterBodyGas sevm base target newPauser oldPauser
        oldCount assignmentCost countCost newCountCost storeCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨post, hrun, hgas, hstore, hlogs, hcompile⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact clean direct-message effects for a **retained** replacement, derived
from the generated-runtime execution: the admin reassigns an already-registered
target from a nonzero `oldPauser` to a nonzero `newPauser`, and `oldPauser`
still holds at least one other assignment afterwards.

The settled state records exactly two events — `PauserSet(target, oldPauser,
newPauser)` and `HeartbeatUpdated(newPauser)` — and the new pauser's heartbeat
expiry is the checked extension.  The absence of a second `HeartbeatUpdated` is
the observable difference from the old-last partition. -/
theorem registerPauser_retainedNonzero_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr} {final settled : Devm}
    (target newPauser oldPauser oldCount newCount nextCount remaining
      timestamp interval expiry currentExpiry expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost storeCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target newPauser)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      replacementRetainedRegisterBodyGas (initSevm msg) (initDevm msg) target
        newPauser oldPauser oldCount assignmentCost countCost newCountCost
        storeCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignment : (initDevm msg).getStorVal ca
      (assignmentSlot target) = oldPauser)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser
      newPauser = assignmentCost)
    (hcount : (assignmentPost (initSevm msg) (initDevm msg) target
      newPauser).getStorVal ca (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hnewCount :
      (foundKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount).getStorVal ca (countSlot newPauser) = newCount)
    (hnewCountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot newPauser) = newCountOriginal)
    (hnewCountNext : (1 : B256) + newCount = nextCount)
    (hnewCountCost : sstoreValueCost newCountOriginal newCount nextCount =
      newCountCost)
    (hremaining : remaining ≠ 0)
    (hremainingCount : (foundNonzeroKernelPost (initSevm msg) (initDevm msg)
      target newPauser oldPauser oldCount nextCount).getStorVal ca
        (countSlot oldPauser) = remaining)
    (htime : (initSevm msg).benvStat.time = timestamp)
    (hinterval : (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target
      newPauser oldPauser oldCount nextCount).getStorVal ca
        heartbeatIntervalSlot = interval)
    (hintervalCold : (ca, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount nextCount).accessedStorageKeys)
    (hexpiry : (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target
      newPauser oldPauser oldCount nextCount).getStorVal ca
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal (initSevm msg) ca
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (ca, expirySlot newPauser) ∈
      (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : (initSevm msg).isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    settled.gasLeft = G ∧
      settled.getStorVal ca (expirySlot newPauser) = expiry ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, oldPauser, newPauser], []⟩,
         ⟨ca, [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  have hdataInit : (initSevm msg).data =
      registerPauserCalldata target newPauser := by
    simpa [initSevm] using hdata
  rcases registerPauserCalldata_spec (initSevm msg) target newPauser
    hdataInit with ⟨hdataLength, hselector, hargTarget, hargNew⟩
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
  rcases registerPauser_runCompiledTo_retainedNonzero dp (initSevm msg)
      (initDevm msg) target newPauser oldPauser oldCount newCount nextCount
      remaining timestamp interval expiry currentExpiry expiryOriginal
      assignmentOriginal countOriginal newCountOriginal assignmentCost
      countCost newCountCost storeCost G hdataLength hvalueInit hselector
      hcodeAddressInit hcodeInit hadminInit hargTarget hargNew htargetValid
      hnewValid holdValid (by simpa [hownerInit] using hassignment)
      (by simpa [hownerInit] using hassignmentOrig) hassignmentCost
      (by simpa [hownerInit] using hcount)
      (by simpa [hownerInit] using hcountOrig) hcountCost
      (by simpa [hownerInit] using hnewCount)
      (by simpa [hownerInit] using hnewCountOrig) hnewCountNext hnewCountCost
      hremaining (by simpa [hownerInit] using hremainingCount) htime
      (by simpa [hownerInit] using hinterval)
      (by simpa [hownerInit] using hintervalCold)
      (by simpa [hownerInit] using hexpiry)
      (by simpa [hownerInit] using hexpiryOrig)
      (by simpa [hownerInit] using hwarmNewExpiry) hstoreCost hgasStipend
      hstatic hextension with
    ⟨post, hrun, hgas, hstore, hlogs, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          replacementRetainedRegisterBodyGas (initSevm msg) (initDevm msg)
            target newPauser oldPauser oldCount assignmentCost countCost
            newCountCost storeCost⟩ =
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
    (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok post)).mpr hexecEq
  change Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hsettledFinal := registerPauser_success_settles_cleanly dp
    htargetOwner howner hcodeAddress hcode hvalue hdata hprocess hclean
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  refine ⟨hgas, ?_, ?_⟩
  · simpa [hownerInit] using hstore
  · simpa [hownerInit] using hlogs

/-! ## Old-last replacement: Registry walk and public boundary -/

/-- Exact `setPauserKernel` reserve for an old-last replacement: the shared
found-nonzero Registry prefix, the new pauser's count read and write, and the
7071 gas plus both expiry value costs of the old-last `finishSetPauser` arm. -/
def replacementOldLastSetPauserKernelGas (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount : B256)
    (assignmentCost countCost newCountCost clearCost storeCost : Nat) : Nat :=
  7071 + clearCost + storeCost +
    (64 + temporalSloadCost sevm
        (foundKernelPost sevm base target newPauser oldPauser oldCount)
        (countSlot newPauser) + newCountCost) +
    foundSetPauserKernelPrefixGas sevm base target newPauser oldPauser
      assignmentCost countCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Complete generated-kernel walk for an **old-last** replacement: the target
is recorded to a nonzero `oldPauser`, the new pauser is nonzero, and the old
pauser's count after the decrement is zero, so `registerAfterSet` clears the old
pauser's heartbeat expiry and emits a zero-payload `HeartbeatUpdated(oldPauser)`
before storing the new pauser's checked expiry.

The old-last restriction is `hcountZero`, which reads the old pauser's count
*out of the walk's own poststate*; the new pauser's interval read, current
expiry and warmth are read out of the poststate of the old-expiry clear.  So
neither the two count slots nor the two expiry slots are assumed disjoint, which
is what lets a new pauser that already holds other targets, or an old pauser
whose expiry slot is not the new pauser's, instantiate this directly.  A
same-pauser call does not: with `oldPauser = newPauser` the count read back is
`nextCount`, so `hcountZero` would demand a wrapped counter.  Its partition is
the retained arm. -/
theorem setPauserKernel_oldLastNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target newPauser oldPauser oldCount newCount nextCount oldExpiry
      oldExpiryOriginal timestamp interval expiry currentExpiry
      expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost clearCost storeCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
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
    (hcountZero : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (countSlot oldPauser) = 0)
    (holdExpiry : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (expirySlot oldPauser) = oldExpiry)
    (holdExpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmOldExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (temporalSstorePost sevm
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount) (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hexpiry : (temporalSstorePost sevm
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount) (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], M,
        G + replacementOldLastSetPauserKernelGas sevm base target newPauser
          oldPauser oldCount assignmentCost countCost newCountCost clearCost
          storeCost⟩)
      setPauserKernel
      (((temporalSstorePost sevm
          (temporalSloadBase sevm
            ((temporalSstorePost sevm
              ((foundNonzeroKernelPost sevm base target newPauser oldPauser
                  oldCount nextCount).addLog
                ⟨sevm.currentTarget,
                  [pauserSetEvent, target, oldPauser, newPauser], []⟩)
              (expirySlot oldPauser) 0).addLog
              ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
                (0 : B256).toBytes⟩)
            heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨[], ((M.write (previousPauserWord * 32).toNat oldPauser.toBytes).write
          0 (0 : B256).toBytes).write 0 expiry.toBytes, G⟩) := by
  have hcovered : (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    rw [hsize]
    decide
  have hsize' :
      (M.write (previousPauserWord * 32).toNat oldPauser.toBytes).size =
        640 := by
    rw [Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using hcovered)]
    exact hsize
  have htarget' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (targetWord * 32).toNat 32 0) = target := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  have hnew' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (newPauserWord * 32).toNat 32 0) =
      newPauser := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew
  have hcontinuation' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (continuationWord * 32).toNat 32 0) =
      0 := by
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      simp only [B256.length_toBytes]
      decide)]
    exact hcontinuation
  have hprevious' : Bytes.toB256
      ((Bytes.writeAt img (previousPauserWord * 32).toNat
        oldPauser.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      oldPauser := by
    have hslice := Bytes.sliceD_writeAt img oldPauser.toBytes
      (previousPauserWord * 32).toNat
    rw [B256.length_toBytes] at hslice
    rw [hslice]
    exact B256.toB256_toBytes oldPauser
  have hwarmOldCount : (sevm.currentTarget, countSlot oldPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys := by
    simp only [foundNonzeroKernelPost, temporalSstorePost_accessedStorageKeys]
    refine temporalSloadBase_preserves_warm _ _ _ _ ?_
    simp only [foundKernelPost, temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_warm _ _ _
  have hfinish := finishSetPauser_oldLastNonzero_runCompiled dp sevm
    (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
      nextCount)
    (M.write (previousPauserWord * 32).toNat oldPauser.toBytes)
    (Bytes.writeAt img (previousPauserWord * 32).toNat oldPauser.toBytes)
    target oldPauser oldExpiry oldExpiryOriginal newPauser timestamp interval
    expiry currentExpiry expiryOriginal [] clearCost storeCost G (by simp)
    (Mem.Wf.write hwf _ _) (Mem.Reads.write hwf hreads _ _) htarget'
    hprevious' hnew' hcontinuation' holdValid.1 hnewNonzero hcountZero
    hwarmOldCount holdExpiry holdExpiryOrig hwarmOldExpiry hclearCost htime
    hinterval hintervalCold hexpiry hexpiryOrig hwarmNewExpiry hstoreCost
    hgasStipend hstatic (by omega) (by rw [hsize'])
    hextension
  dsimp only [foundNonzeroKernelPost] at hfinish
  have hkernel := setPauserKernel_foundNonzero_finishSetPauser_runCompiled dp
    sevm base M img _ target newPauser oldPauser oldCount newCount nextCount
    assignmentOriginal countOriginal newCountOriginal assignmentCost countCost
    newCountCost (G + 7071 + clearCost + storeCost) hwf hreads htarget hnew
    htargetValid holdValid hnewNonzero hsize hassignment hassignmentOrig
    hassignmentCost hcount hcountOrig hcountCost hnewCount hnewCountOrig
    hnewCountNext hnewCountCost (by omega) hstatic hfinish
  have hg : G + replacementOldLastSetPauserKernelGas sevm base target
        newPauser oldPauser oldCount assignmentCost countCost newCountCost
        clearCost storeCost =
      G + 7071 + clearCost + storeCost +
        (64 + temporalSloadCost sevm
          (foundKernelPost sevm base target newPauser oldPauser oldCount)
          (countSlot newPauser) + newCountCost) +
        foundSetPauserKernelPrefixGas sevm base target newPauser oldPauser
          assignmentCost countCost := by
    dsimp only [replacementOldLastSetPauserKernelGas]
    omega
  rw [hg]
  exact hkernel

/-- Exact production-body reserve for an old-last replacement. -/
def replacementOldLastRegisterBodyGas (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount : B256)
    (assignmentCost countCost newCountCost clearCost storeCost : Nat) : Nat :=
  221 + replacementOldLastSetPauserKernelGas sevm base target newPauser
    oldPauser oldCount assignmentCost countCost newCountCost clearCost
    storeCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact successful production body for an **old-last** replacement: an
admin-authorised `registerPauser(target, newPauser)` on a target already
recorded to a nonzero `oldPauser`, with a nonzero `newPauser`, where the old
pauser holds no other assignment afterwards.

Three records are emitted, in order: `PauserSet(target, oldPauser, newPauser)`,
a zero-payload `HeartbeatUpdated(oldPauser)` retiring the old pauser's
heartbeat, and `HeartbeatUpdated(newPauser)` carrying the checked extension. -/
theorem registerPauser_body_oldLastNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount newCount nextCount oldExpiry
      oldExpiryOriginal timestamp interval expiry currentExpiry
      expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost clearCost storeCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = newPauser)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (holdValid : nonzeroCanonicalAddress oldPauser)
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
    (hcountZero : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (countSlot oldPauser) = 0)
    (holdExpiry : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (expirySlot oldPauser) = oldExpiry)
    (holdExpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmOldExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (temporalSstorePost sevm
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount) (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hexpiry : (temporalSstorePost sevm
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount) (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + replacementOldLastRegisterBodyGas sevm base target newPauser
            oldPauser oldCount assignmentCost countCost newCountCost clearCost
            storeCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, oldPauser, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, oldPauser], (0 : B256).toBytes⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  rcases registerMemory_spec target newPauser with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      _hpreviousRead, hcontinuationRead⟩
  have hkernel := setPauserKernel_oldLastNonzero_runCompiled dp sevm base
    (registerMemory target newPauser) (registerImage target newPauser)
    target newPauser oldPauser oldCount newCount nextCount oldExpiry
    oldExpiryOriginal timestamp interval expiry currentExpiry expiryOriginal
    assignmentOriginal countOriginal newCountOriginal assignmentCost countCost
    newCountCost clearCost storeCost G hwf hreads htargetRead hnewRead
    hcontinuationRead htargetValid holdValid hnewValid.1 hsize hassignment
    hassignmentOrig hassignmentCost hcount hcountOrig hcountCost hnewCount
    hnewCountOrig hnewCountNext hnewCountCost hcountZero holdExpiry
    holdExpiryOrig hwarmOldExpiry hclearCost htime hinterval hintervalCold
    hexpiry hexpiryOrig hwarmNewExpiry hstoreCost hgasStipend hstatic
    hextension
  have hstage := registerPauser_stageArgs_runCompiled dp sevm base target
    newPauser
    (G + replacementOldLastSetPauserKernelGas sevm base target newPauser
      oldPauser oldCount assignmentCost countCost newCountCost clearCost
      storeCost)
    _ hargTarget hargNew hkernel
  have hbody : Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[], Mem.empty,
        G + replacementOldLastRegisterBodyGas sevm base target newPauser
          oldPauser oldCount assignmentCost countCost newCountCost clearCost
          storeCost⟩)
      (registerPauser dp)
      (((temporalSstorePost sevm
          (temporalSloadBase sevm
            ((temporalSstorePost sevm
              ((foundNonzeroKernelPost sevm base target newPauser oldPauser
                  oldCount nextCount).addLog
                ⟨sevm.currentTarget,
                  [pauserSetEvent, target, oldPauser, newPauser], []⟩)
              (expirySlot oldPauser) 0).addLog
              ⟨sevm.currentTarget, [heartbeatUpdatedEvent, oldPauser],
                (0 : B256).toBytes⟩)
            heartbeatIntervalSlot)
          (expirySlot newPauser) expiry).addLog
        ⟨sevm.currentTarget, [heartbeatUpdatedEvent, newPauser],
          expiry.toBytes⟩).setMach
        ⟨[], (((registerMemory target newPauser).write
          (previousPauserWord * 32).toNat oldPauser.toBytes).write
          0 (0 : B256).toBytes).write 0 expiry.toBytes, G⟩) := by
    have htargetMask := canonicalAddress_mask_zero htargetValid.2
    have hnewMask := canonicalAddress_mask_zero hnewValid.2
    unfold registerPauser requireStaticArgs canonicalAddressArg onlyAdmin arg
      cdl checkNonAddress pushAddressMask pushDeployWord
    func_run (24) [0, ~~~(0 : B256), addressMask, 0,
      ~~~(0 : B256), addressMask, 0, 1]
    all_goals try { rw [hargTarget]; exact htargetMask }
    all_goals try { rw [hargNew]; exact hnewMask }
    all_goals try { simp [hadmin, B256.eqCheck] }
    all_goals first
      | (simp only [Devm.gasLeft_setMach, replacementOldLastRegisterBodyGas]
         norm_num [gBase, gVerylow, gHigh, gMid, gJumpdest]
         omega)
      | skip
    case h_arm =>
      simp only [replacementOldLastRegisterBodyGas]
      have hg : G + (221 + replacementOldLastSetPauserKernelGas sevm base
            target newPauser oldPauser oldCount assignmentCost countCost
            newCountCost clearCost storeCost) - 109 =
          G + replacementOldLastSetPauserKernelGas sevm base target newPauser
            oldPauser oldCount assignmentCost countCost newCountCost clearCost
            storeCost + 112 := by
        omega
      rw [hg]
      simpa only [arg, cdl] using hstage
  refine ⟨_, hbody, rfl, ?_, ?_⟩
  · have getStorVal_setMach (d : Devm) (mach : Mach) (a : Adr) (k : B256) :
        (d.setMach mach).getStorVal a k = d.getStorVal a k := rfl
    have getStorVal_addLog (d : Devm) (l : Log) (a : Adr) (k : B256) :
        (d.addLog l).getStorVal a k = d.getStorVal a k := rfl
    rw [getStorVal_setMach, getStorVal_addLog, temporalSstorePost_self]
  · have logs_setMach (d : Devm) (mach : Mach) :
        (d.setMach mach).logs = d.logs := rfl
    have logs_addLog (d : Devm) (l : Log) :
        (d.addLog l).logs = d.logs ++ [l] := rfl
    have hkernelLogs : (foundNonzeroKernelPost sevm base target newPauser
        oldPauser oldCount nextCount).logs = base.logs := by
      simp only [foundNonzeroKernelPost]
      rw [temporalSstorePost_logs, temporalSloadBase_logs]
      simp only [foundKernelPost]
      rw [temporalSstorePost_logs, temporalSloadBase_logs]
      simp only [assignmentPost]
      rw [temporalSstorePost_logs]
      simp only [assignmentBase]
      rw [temporalSloadBase_logs]
    rw [logs_setMach, logs_addLog, temporalSstorePost_logs,
      temporalSloadBase_logs, logs_addLog, temporalSstorePost_logs,
      logs_addLog, hkernelLogs]
    simp only [List.append_assoc]
    rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-runtime success for an **old-last** replacement: the
dispatcher's own reserve above `registerPauser_body_oldLastNonzero_runCompiled`,
with the same effects. -/
theorem registerPauser_runCompiledTo_oldLastNonzero
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (target newPauser oldPauser oldCount newCount nextCount oldExpiry
      oldExpiryOriginal timestamp interval expiry currentExpiry
      expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost clearCost storeCost G : Nat)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = newPauser)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (holdValid : nonzeroCanonicalAddress oldPauser)
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
    (hcountZero : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (countSlot oldPauser) = 0)
    (holdExpiry : (foundNonzeroKernelPost sevm base target newPauser oldPauser
      oldCount nextCount).getStorVal sevm.currentTarget
        (expirySlot oldPauser) = oldExpiry)
    (holdExpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmOldExpiry : (sevm.currentTarget, expirySlot oldPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : (temporalSstorePost sevm
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount) (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hexpiry : (temporalSstorePost sevm
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount) (expirySlot oldPauser) 0).getStorVal sevm.currentTarget
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (foundNonzeroKernelPost sevm base target newPauser oldPauser oldCount
        nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            replacementOldLastRegisterBodyGas sevm base target newPauser
              oldPauser oldCount assignmentCost countCost newCountCost
              clearCost storeCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, oldPauser, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, oldPauser], (0 : B256).toBytes⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_oldLastNonzero_runCompiled dp sevm base target
      newPauser oldPauser oldCount newCount nextCount oldExpiry
      oldExpiryOriginal timestamp interval expiry currentExpiry expiryOriginal
      assignmentOriginal countOriginal newCountOriginal assignmentCost
      countCost newCountCost clearCost storeCost G hbodyData hadmin hargTarget
      hargNew htargetValid hnewValid holdValid hassignment hassignmentOrig
      hassignmentCost hcount hcountOrig hcountCost hnewCount hnewCountOrig
      hnewCountNext hnewCountCost hcountZero holdExpiry holdExpiryOrig
      hwarmOldExpiry hclearCost htime hinterval hintervalCold hexpiry
      hexpiryOrig hwarmNewExpiry hstoreCost hgasStipend hstatic
      hextension with
    ⟨post, hbody, hgas, hstore, hlogs⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (replacementOldLastRegisterBodyGas sevm base target newPauser oldPauser
        oldCount assignmentCost countCost newCountCost clearCost storeCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨post, hrun, hgas, hstore, hlogs, hcompile⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact clean direct-message effects for an **old-last** replacement, derived
from the generated-runtime execution: the admin reassigns an already-registered
target from a nonzero `oldPauser` to a nonzero `newPauser`, and `oldPauser` is
left holding no assignment at all.

The settled state records exactly three events, and the retired pauser's
`HeartbeatUpdated` carries a 32-byte zero payload — the observable difference
from the retained partition. -/
theorem registerPauser_oldLastNonzero_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr} {final settled : Devm}
    (target newPauser oldPauser oldCount newCount nextCount oldExpiry
      oldExpiryOriginal timestamp interval expiry currentExpiry
      expiryOriginal : B256)
    (assignmentOriginal countOriginal newCountOriginal : B256)
    (assignmentCost countCost newCountCost clearCost storeCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target newPauser)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      replacementOldLastRegisterBodyGas (initSevm msg) (initDevm msg) target
        newPauser oldPauser oldCount assignmentCost countCost newCountCost
        clearCost storeCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (holdValid : nonzeroCanonicalAddress oldPauser)
    (hassignment : (initDevm msg).getStorVal ca
      (assignmentSlot target) = oldPauser)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal oldPauser
      newPauser = assignmentCost)
    (hcount : (assignmentPost (initSevm msg) (initDevm msg) target
      newPauser).getStorVal ca (countSlot oldPauser) = oldCount)
    (hcountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot oldPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal oldCount (oldCount - 1) =
      countCost)
    (hnewCount :
      (foundKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount).getStorVal ca (countSlot newPauser) = newCount)
    (hnewCountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot newPauser) = newCountOriginal)
    (hnewCountNext : (1 : B256) + newCount = nextCount)
    (hnewCountCost : sstoreValueCost newCountOriginal newCount nextCount =
      newCountCost)
    (hcountZero : (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target
      newPauser oldPauser oldCount nextCount).getStorVal ca
        (countSlot oldPauser) = 0)
    (holdExpiry : (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target
      newPauser oldPauser oldCount nextCount).getStorVal ca
        (expirySlot oldPauser) = oldExpiry)
    (holdExpiryOrig : getOrigStorVal (initSevm msg) ca
      (expirySlot oldPauser) = oldExpiryOriginal)
    (hwarmOldExpiry : (ca, expirySlot oldPauser) ∈
      (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount nextCount).accessedStorageKeys)
    (hclearCost : sstoreValueCost oldExpiryOriginal oldExpiry 0 = clearCost)
    (htime : (initSevm msg).benvStat.time = timestamp)
    (hinterval : (temporalSstorePost (initSevm msg)
      (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount nextCount) (expirySlot oldPauser) 0).getStorVal ca
        heartbeatIntervalSlot = interval)
    (hintervalCold : (ca, heartbeatIntervalSlot) ∉
      (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount nextCount).accessedStorageKeys)
    (hexpiry : (temporalSstorePost (initSevm msg)
      (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount nextCount) (expirySlot oldPauser) 0).getStorVal ca
        (expirySlot newPauser) = currentExpiry)
    (hexpiryOrig : getOrigStorVal (initSevm msg) ca
      (expirySlot newPauser) = expiryOriginal)
    (hwarmNewExpiry : (ca, expirySlot newPauser) ∈
      (foundNonzeroKernelPost (initSevm msg) (initDevm msg) target newPauser
        oldPauser oldCount nextCount).accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal currentExpiry expiry =
      storeCost)
    (hgasStipend : gCallStipend < G + 1395 + storeCost)
    (hstatic : (initSevm msg).isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    settled.gasLeft = G ∧
      settled.getStorVal ca (expirySlot newPauser) = expiry ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, oldPauser, newPauser], []⟩,
         ⟨ca, [heartbeatUpdatedEvent, oldPauser], (0 : B256).toBytes⟩,
         ⟨ca, [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  have hdataInit : (initSevm msg).data =
      registerPauserCalldata target newPauser := by
    simpa [initSevm] using hdata
  rcases registerPauserCalldata_spec (initSevm msg) target newPauser
    hdataInit with ⟨hdataLength, hselector, hargTarget, hargNew⟩
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
  rcases registerPauser_runCompiledTo_oldLastNonzero dp (initSevm msg)
      (initDevm msg) target newPauser oldPauser oldCount newCount nextCount
      oldExpiry oldExpiryOriginal timestamp interval expiry currentExpiry
      expiryOriginal assignmentOriginal countOriginal newCountOriginal
      assignmentCost countCost newCountCost clearCost storeCost G hdataLength
      hvalueInit hselector hcodeAddressInit hcodeInit hadminInit hargTarget
      hargNew htargetValid hnewValid holdValid
      (by simpa [hownerInit] using hassignment)
      (by simpa [hownerInit] using hassignmentOrig) hassignmentCost
      (by simpa [hownerInit] using hcount)
      (by simpa [hownerInit] using hcountOrig) hcountCost
      (by simpa [hownerInit] using hnewCount)
      (by simpa [hownerInit] using hnewCountOrig) hnewCountNext hnewCountCost
      (by simpa [hownerInit] using hcountZero)
      (by simpa [hownerInit] using holdExpiry)
      (by simpa [hownerInit] using holdExpiryOrig)
      (by simpa [hownerInit] using hwarmOldExpiry) hclearCost htime
      (by simpa [hownerInit] using hinterval)
      (by simpa [hownerInit] using hintervalCold)
      (by simpa [hownerInit] using hexpiry)
      (by simpa [hownerInit] using hexpiryOrig)
      (by simpa [hownerInit] using hwarmNewExpiry) hstoreCost hgasStipend
      hstatic hextension with
    ⟨post, hrun, hgas, hstore, hlogs, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          replacementOldLastRegisterBodyGas (initSevm msg) (initDevm msg)
            target newPauser oldPauser oldCount assignmentCost countCost
            newCountCost clearCost storeCost⟩ =
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
    (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok post)).mpr hexecEq
  change Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hsettledFinal := registerPauser_success_settles_cleanly dp
    htargetOwner howner hcodeAddress hcode hvalue hdata hprocess hclean
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  refine ⟨hgas, ?_, ?_⟩
  · simpa [hownerInit] using hstore
  · simpa [hownerInit] using hlogs

end Blanc.LidoCircuitBreaker
