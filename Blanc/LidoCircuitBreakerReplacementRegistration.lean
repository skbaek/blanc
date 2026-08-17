import Blanc.LidoCircuitBreakerRegistrySubstrate

/-!
Replacement chronology for the Lido CircuitBreaker.

The target is already registered to a nonzero previous pauser and the new pauser
is nonzero, so `setPauser` replaces the assignment, decrements the old pauser's
count and increments the new pauser's — the three-write found-nonzero Registry
walk of `setPauserKernel_foundNonzero_finishSetPauser_runCompiled`.

`registerAfterSet` then branches on the old pauser's *remaining* count.  This
module carries the **old-last** arm, where that count is zero: the old pauser's
heartbeat expiry is cleared and a second `HeartbeatUpdated` is emitted before the
shared nonzero-new-pauser suffix runs.  The retained arm (remaining count
nonzero) is a different chronology and is not proved here.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst


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

end Blanc.LidoCircuitBreaker
