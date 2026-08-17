import Blanc.LidoCircuitBreakerRegistrySubstrate

/-!
Fresh-registration chronology for the Lido CircuitBreaker.

The target is absent from the registry and the new pauser's entry count is
nonzero, so `setPauser` appends the target and takes the five-write
fresh-nonzero chronology.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst


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

private theorem size_writeZero_word_of_le
    {M : Mem} {w : B256} (h : 32 ≤ M.size) :
    (M.write 0 w.toBytes).size = M.size := by
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp)
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, hlen, Nat.zero_add]
    rw [if_pos h]
    split <;> rfl

private theorem temporalSloadBase_preserves_cold
    (sevm : Sevm) (base : Devm) (readKey key : B256)
    (hne : readKey ≠ key)
    (h : (sevm.currentTarget, key) ∉ base.accessedStorageKeys) :
    (sevm.currentTarget, key) ∉
      (temporalSloadBase sevm base readKey).accessedStorageKeys := by
  unfold temporalSloadBase
  split
  · exact h
  · rcases base with ⟨mach, mt, world⟩
    simpa [addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      And.intro hne h

/-- The fresh/nonzero model branch determines the exact five-write source
trace and its refined Registry witness.  This is the semantic target used by
the forward emitted-kernel construction below; no trace or poststate is
supplied by the caller. -/
theorem freshRegistration_sourceTrace_witness
    {s : Stor} {entries : List Entry} {target newPauser : B256}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = none) :
    ∃ trace : SetPauserSourceTrace,
      setPauserSourceTrace entries target newPauser = some trace ∧
      trace.postEntries = entries ++ [(target, newPauser)] ∧
      trace.writes =
        [(assignmentSlot target, newPauser),
          (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
          (indexSlot target, Nat.toB256 (entries.length + 1)),
          (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
          (countSlot newPauser,
            Nat.toB256 (assignmentCount entries newPauser + 1))] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites s trace.writes))
        trace.postEntries := by
  let writes : List (B256 × B256) :=
    [(assignmentSlot target, newPauser),
      (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
      (indexSlot target, Nat.toB256 (entries.length + 1)),
      (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
      (countSlot newPauser,
        Nat.toB256 (assignmentCount entries newPauser + 1))]
  let trace : SetPauserSourceTrace :=
    { postEntries := entries ++ [(target, newPauser)]
      writes := writes }
  refine ⟨trace, ?_, rfl, rfl, ?_⟩
  · simp [trace, writes, setPauserSourceTrace, setPauser,
      htarget.1, hfind, hnew.1, setPauserSourceWrites,
      Option.getD]
  · dsimp only [trace, writes]
    exact hw.applyFreshWrites htarget hnew hfind

set_option maxRecDepth 8192 in
private theorem registerAfterSet_storeLogTail_freshNonzero
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (newPauser expiry carry : B256) (G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hsize : 640 ≤ M.size)
    (halign : M.size % 32 = 0)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[expirySlot newPauser, expiry, carry],
          M.write 0 expiry.toBytes, G + 21395⟩)
        (Ninst.sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop) post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  let M' := M.write 0 expiry.toBytes
  have hsizeM' : M'.size = M.size :=
    size_writeZero_word_of_le (by omega)
  have hsize' : 640 ≤ M'.size := by rw [hsizeM']; exact hsize
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have hnewCovered' :
      (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewValue' :
      (M'.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [readNewPauser_after_writeZero hwf hreads]
    rw [Mem.Reads.read hreads]
    exact hnew
  have hnewMemory' :
      (M'.read (newPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hnewCovered')]
  have hexpiryBytes : expiry.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes expiry
    rw [h] at hlen
    simp at hlen
  let pre := base.setMach
    ⟨[expirySlot newPauser, expiry, carry], M', G + 21395⟩
  let rc := sstoreNewRefundCounter expiry 0 0 base.refundCounter
  let inter := ((pre.withRefundCounter rc).setStorVal
      sevm.currentTarget (expirySlot newPauser) expiry).setMach
      ⟨[carry], M', G + 1395⟩
  have hsstore : Ninst.RunCompiled sevm pre (.reg .sstore) inter := by
    apply Ninst.runCompiled_sstore_warm
      (c := gasStorageSet) (G := G + 1395) (rc := rc)
    · rfl
    · change (sevm.currentTarget, expirySlot newPauser) ∈
        base.accessedStorageKeys
      exact hwarmExpiry
    · simp only [pre, Devm.gasLeft_setMach]
      norm_num [gCallStipend]
    · exact hstatic
    · rw [hexpiryOrig, Devm.getStorVal_setMach, hexpiry]
      simp [sstoreValueCost, gasStorageSet]
      intro h
      exact False.elim (hexpiryNonzero h.symm)
    · have refundCounter_setMach (d : Devm) (mach : Mach) :
          (d.setMach mach).refundCounter = d.refundCounter := rfl
      simp only [pre, rc, refundCounter_setMach,
        Devm.getStorVal_setMach]
      rw [hexpiryOrig, hexpiry]
    · simp only [pre, Devm.gasLeft_setMach]
      norm_num [gasStorageSet]
  have htail : ∃ post,
      Func.RunCompiled fs sevm inter
        (loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop) post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
    apply Exists.intro
    constructor
    · func_run [3, 1381]
      all_goals try {
        simp only [inter, Devm.stack_setMach, Devm.gasLeft_setMach]
        omega }
      case h_room =>
        simp only [inter, Devm.stack_setMach, List.length_cons,
          List.length_nil]
        decide
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
    · refine ⟨?_, ?_, ?_⟩
      · simp only [Devm.gasLeft_setMach]
        omega
      · rw [Devm.getStorVal_setMach]
        have getStorVal_addLog (d : Devm) (log : Log)
            (a : Adr) (k : B256) :
            (d.addLog log).getStorVal a k = d.getStorVal a k := rfl
        rw [getStorVal_addLog, Devm.getStorVal_setMach]
        show (Devm.getStor _ sevm.currentTarget).get
          (expirySlot newPauser) = expiry
        rw [setStorVal_getStor_self, Stor.get_set_self]
      · have logs_setMach (d : Devm) (mach : Mach) :
            (d.setMach mach).logs = d.logs := rfl
        have logs_addLog (d : Devm) (log : Log) :
            (d.addLog log).logs = d.logs ++ [log] := rfl
        have logs_setStorVal (d : Devm) (a : Adr) (k v : B256) :
            (d.setStorVal a k v).logs = d.logs := rfl
        have logs_withRefundCounter (d : Devm) (rc : Int) :
            (d.withRefundCounter rc).logs = d.logs := rfl
        rw [logs_setMach, logs_addLog, logs_setMach, logs_setStorVal,
          logs_withRefundCounter, logs_setMach]
        rw [hnewValue', hnewMemory']
        rw [show ((0 : B256) * 32).toNat = 0 by decide,
          show ((1 : B256) * 32).toNat = 32 by decide]
        simp only [M']
        have hread :
            ((M.write 0 expiry.toBytes).read 0 32).1 = expiry.toBytes := by
          simpa only [B256.length_toBytes] using
            (Mem.read_write_zero M hexpiryBytes)
        rw [hread]
  rcases htail with ⟨post, hrun, hgas, hstore, hlogs⟩
  exact ⟨post, Func.RunCompiled.next hsstore hrun,
    hgas, hstore, hlogs⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem registerAfterSet_freshNonzero_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (newPauser timestamp interval expiry carry : B256)
    (G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hnewNonzero : newPauser ≠ 0)
    (hsize : 640 ≤ M.size)
    (halign : M.size % 32 = 0)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hintervalCold :
      (sevm.currentTarget, heartbeatIntervalSlot) ∉
        base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[carry], M, G + 23592⟩)
        registerAfterSet post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
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
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [Mem.Reads.read hreads]
    exact hnew
  have hsum := CheckedHeartbeatExtension.add_eq hextension
  have hle : timestamp ≤ expiry := by
    rcases hextension with ⟨bound, rfl⟩
    rw [B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt bound]
    omega
  let M' := M.write 0 expiry.toBytes
  have hsizeM' : M'.size = M.size :=
    size_writeZero_word_of_le (by omega)
  have halignM' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have hnewCoveredM' :
      (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    exact hnewCovered
  have hnewValueM' :
      (M'.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [readNewPauser_after_writeZero hwf hreads]
    exact hnewValue
  have hnewMemoryM' :
      (M'.read (newPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halignM' hnewCoveredM')]
  let afterInterval :=
    addAccessedStorageKey base sevm.currentTarget heartbeatIntervalSlot
  have hexpiryAfter : afterInterval.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0 := by
    change base.getStorVal sevm.currentTarget (expirySlot newPauser) = 0
    exact hexpiry
  have hwarmExpiryAfter :
      (sevm.currentTarget, expirySlot newPauser) ∈
        afterInterval.accessedStorageKeys := by
    rcases base with ⟨mach, mt, world⟩
    simpa [afterInterval, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      (Or.inr hwarmExpiry :
        heartbeatIntervalSlot = expirySlot newPauser ∨
          (sevm.currentTarget, expirySlot newPauser) ∈
            mt.accessedStorageKeys)
  rcases registerAfterSet_storeLogTail_freshNonzero fs sevm afterInterval
      M img newPauser expiry carry G hwf hreads hnew hsize halign
      hexpiryAfter hexpiryOrig hwarmExpiryAfter hstatic hexpiryNonzero with
    ⟨post, htail, hgas, hstore, hlogs⟩
  refine ⟨post, ?_, hgas, hstore, ?_⟩
  · simp only [registerAfterSet]
    func_run (24) [3, 1, 3, 0, expiry, 0, 0, 3,
      expirySlot newPauser]
    all_goals try {
      simp [hpreviousValue, htime, hle, B256.eqCheck, B256.ltCheck] }
    all_goals try {
      rw [Devm.extCost_zero_of_le halign hpreviousCovered]
      norm_num [gVerylow] }
    case h_cost =>
      rw [hpreviousMemory]
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow]
    case h_val =>
      rw [hpreviousMemory, hnewValue]
      simp [B256.eqCheck, hnewNonzero]
    case h_val =>
      rw [hpreviousMemory, hnewMemory]
      simp only [Devm.getStorVal_setMach]
      rw [hinterval, htime, B256.add_comm, hsum]
    case h_ext =>
      rw [hpreviousMemory, hnewMemory]
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_zero_of_le halign (by omega)]
    case h_cost =>
      rw [hpreviousMemory, hnewMemory]
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      change gVerylow +
        ((addAccessedStorageKey base sevm.currentTarget
          heartbeatIntervalSlot).setMach
          ⟨_, M', _⟩).extCost
            [⟨(newPauserWord * 32).toNat, 32⟩] = 3
      rw [Devm.extCost_zero_of_le halignM' hnewCoveredM']
      norm_num [gVerylow]
    case h_val =>
      rw [hpreviousMemory, hnewMemory]
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      change (regionWord expiryRegion).or
        (M'.read (newPauserWord * 32).toNat 32).1.toB256 = _
      rw [hnewValueM']
      rfl
    case a =>
      rw [addAccessedStorageKey_setMach_setMach]
      rw [hpreviousMemory]
      rw [hnewMemory]
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [hnewMemoryM']
      exact htail
  · have logsAfter : afterInterval.logs = base.logs := rfl
    rw [logsAfter] at hlogs
    exact hlogs

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem finishSetPauser_freshNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target newPauser timestamp interval expiry carry : B256)
    (G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (hnewNonzero : newPauser ≠ 0)
    (hsize : 640 ≤ M.size)
    (halign : M.size % 32 = 0)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hintervalCold :
      (sevm.currentTarget, heartbeatIntervalSlot) ∉
        base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ post,
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[carry], M, G + 25527⟩) finishSetPauser post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, 0, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, newPauser], []⟩
  let eventBase := base.addLog eventLog
  have hintervalEvent : eventBase.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval := by
    change base.getStorVal sevm.currentTarget heartbeatIntervalSlot = interval
    exact hinterval
  have hintervalColdEvent :
      (sevm.currentTarget, heartbeatIntervalSlot) ∉
        eventBase.accessedStorageKeys := by
    change (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys
    exact hintervalCold
  have hexpiryEvent : eventBase.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0 := by
    change base.getStorVal sevm.currentTarget (expirySlot newPauser) = 0
    exact hexpiry
  have hwarmExpiryEvent :
      (sevm.currentTarget, expirySlot newPauser) ∈
        eventBase.accessedStorageKeys := by
    change (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys
    exact hwarmExpiry
  rcases registerAfterSet_freshNonzero_runCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm eventBase M img
      newPauser timestamp interval expiry carry G hwf hreads hprevious hnew
      hnewNonzero hsize halign htime hintervalEvent hintervalColdEvent
      hexpiryEvent hexpiryOrig hwarmExpiryEvent hstatic hextension
      hexpiryNonzero with ⟨post, hregister, hgas, hstore, hlogs⟩
  refine ⟨post, ?_, hgas, hstore, ?_⟩
  · have h := finishSetPauser_registerAfterSet_runCompiled dp sevm base M img
      target 0 newPauser [carry] (G + 23592) post (by simp)
      hreads htarget hprevious hnew hcontinuation hsize halign hstatic
      hregister
    have hg : G + 23592 + 1935 = G + 25527 := by omega
    rw [hg] at h
    exact h
  · have heventLogs : eventBase.logs = base.logs ++ [eventLog] := rfl
    rw [heventLogs] at hlogs
    simpa [eventLog, List.append_assoc] using hlogs

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem afterOldPauser_freshNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target newPauser timestamp interval expiry count nextCount carry : B256)
    (countOriginal : B256) (countCost G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (hsize : 640 ≤ M.size)
    (halign : M.size % 32 = 0)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot newPauser) = count)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot newPauser) = countOriginal)
    (hcountNext : (1 : B256) + count = nextCount)
    (hcountCost : sstoreValueCost countOriginal count nextCount = countCost)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ post,
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[carry], M,
          G + 25591 + temporalSloadCost sevm base
            (countSlot newPauser) + countCost⟩)
        afterOldPauser post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, 0, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  let countKey := countSlot newPauser
  let countBase := temporalSloadBase sevm base countKey
  let countPost := temporalSstorePost sevm countBase countKey nextCount
  have hcountInterval : countKey ≠ heartbeatIntervalSlot := by
    simpa only [countKey, countSlot, heartbeatIntervalSlot] using
      slot_ne_of_region_ne
        (leftRegion := countRegion) (rightRegion := configRegion)
        (by norm_num [countRegion]) (by norm_num [configRegion])
        (canonicalAddress_payload_lt hnewValid.2)
        (by change (1 : Nat) < 2 ^ 252; norm_num)
        (by norm_num [countRegion, configRegion])
  have hcountExpiry : countKey ≠ expirySlot newPauser := by
    exact Ne.symm
      (expirySlot_ne_registryAddressFamilies hnewValid.2 hnewValid.2
        hnewValid.2).2.2
  have hintervalPost : countPost.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval := by
    rw [temporalSstorePost_other sevm countBase countKey nextCount
      sevm.currentTarget heartbeatIntervalSlot (by
        intro hpair
        exact hcountInterval (congrArg Prod.snd hpair).symm)]
    rw [temporalSloadBase_getStorVal]
    exact hinterval
  have hexpiryPost : countPost.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0 := by
    rw [temporalSstorePost_other sevm countBase countKey nextCount
      sevm.currentTarget (expirySlot newPauser) (by
        intro hpair
        exact hcountExpiry (congrArg Prod.snd hpair).symm)]
    rw [temporalSloadBase_getStorVal]
    exact hexpiry
  have hintervalColdPost :
      (sevm.currentTarget, heartbeatIntervalSlot) ∉
        countPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_cold sevm base countKey
      heartbeatIntervalSlot hcountInterval hintervalCold
  have hwarmExpiryPost :
      (sevm.currentTarget, expirySlot newPauser) ∈
        countPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm sevm base countKey
      (expirySlot newPauser) hwarmExpiry
  rcases finishSetPauser_freshNonzero_runCompiled dp sevm countPost M img
      target newPauser timestamp interval expiry carry G hwf hreads htarget
      hprevious hnew hcontinuation hnewValid.1 hsize halign htime
      hintervalPost hintervalColdPost hexpiryPost hexpiryOrig
      hwarmExpiryPost hstatic hextension hexpiryNonzero with
    ⟨post, hfinish, hgas, hstoreExpiry, hlogs⟩
  refine ⟨post, ?_, hgas, hstoreExpiry, ?_⟩
  · have h := afterOldPauser_finishSetPauser_runCompiled dp sevm base M img
      newPauser count nextCount countOriginal [carry] countCost (G + 25527)
      post (by simp) hreads hnew hnewValid.1 (by omega) halign hcount
      hcountOrig hcountNext hcountCost
      (by norm_num [gCallStipend]; omega) hstatic hfinish
    have hg : G + 25527 + 64 +
        temporalSloadCost sevm base (countSlot newPauser) + countCost =
        G + 25591 +
          temporalSloadCost sevm base (countSlot newPauser) + countCost := by
      omega
    rw [hg] at h
    exact h
  · rw [temporalSstorePost_logs, temporalSloadBase_logs] at hlogs
    exact hlogs

private theorem appendTarget_freshNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target newPauser timestamp interval expiry length next count nextCount : B256)
    (arrayOriginal indexOriginal lengthOriginal countOriginal : B256)
    (arrayCost indexCost lengthCost countCost G : Nat)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (hnextBound : next.toNat < 2 ^ 252)
    (hnextNonzero : next ≠ 0)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (hmemoryShape : M.size = 640 ∨ M.size = 672 ∨
      (arrayLengthWord * 32).toNat + 32 ≤ M.size)
    (htime : sevm.benvStat.time = timestamp)
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
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot newPauser) = count)
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot newPauser) = countOriginal)
    (hcountNext : (1 : B256) + count = nextCount)
    (hcountCost : sstoreValueCost countOriginal count nextCount = countCost)
    (hcountCold : (sevm.currentTarget, countSlot newPauser) ∉
      base.accessedStorageKeys)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hexpiry : base.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ post,
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M,
          G + 25666 + arrayLengthMemoryCost M +
            temporalSloadCost sevm base arrayLengthSlot +
            arrayCost + indexCost + lengthCost +
            temporalSloadCost sevm
              (temporalSstorePost sevm
                (temporalSstorePost sevm
                  (temporalSstorePost sevm
                    (temporalSloadBase sevm base arrayLengthSlot)
                    (arrayEntrySlot next) target)
                  (indexSlot target) next)
                arrayLengthSlot next)
              (countSlot newPauser) + countCost⟩)
        appendTarget post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, 0, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let countKey := countSlot newPauser
  let lengthBase := temporalSloadBase sevm base arrayLengthSlot
  let arrayPost := temporalSstorePost sevm lengthBase arrayKey target
  let indexPost := temporalSstorePost sevm arrayPost indexKey next
  let lengthPost := temporalSstorePost sevm indexPost arrayLengthSlot next
  let afterGas := G + 25591 + temporalSloadCost sevm lengthPost countKey + countCost
  have hfamilies := registryAddressFamilies_pairwise
    htargetValid.2 htargetValid.2 hnewValid.2
  have harrayFamilies := registryAddressFamilies_ne_arrayEntrySlot
    htargetValid.2 hnewValid.2 hnextBound
  have hlengthFamilies := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 hnewValid.2
  have hlengthArray :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnextNonzero hnextBound
  have hlengthInterval : arrayLengthSlot ≠ heartbeatIntervalSlot := by
    simpa only [arrayLengthSlot, heartbeatIntervalSlot] using
      slot_ne_of_region_ne
        (leftRegion := arrayRegion) (rightRegion := configRegion)
        (left := (0 : B256)) (right := (1 : B256))
        (by norm_num [arrayRegion]) (by norm_num [configRegion])
        (by change (0 : Nat) < 2 ^ 252; norm_num)
        (by change (1 : Nat) < 2 ^ 252; norm_num)
        (by norm_num [arrayRegion, configRegion])
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
    temporalSloadBase_preserves_warm sevm base arrayLengthSlot arrayKey hwarmArray
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
  have hcountPost : lengthPost.getStorVal sevm.currentTarget countKey = count := by
    rw [temporalSstorePost_other sevm indexPost arrayLengthSlot next
      sevm.currentTarget countKey (pairNe (by
        simpa only [countKey] using hlengthFamilies.2.2))]
    rw [temporalSstorePost_other sevm arrayPost indexKey next
      sevm.currentTarget countKey (pairNe (Ne.symm hfamilies.2.2))]
    rw [temporalSstorePost_other sevm lengthBase arrayKey target
      sevm.currentTarget countKey (pairNe (by
        simpa only [arrayKey, countKey] using harrayFamilies.2.2))]
    rw [temporalSloadBase_getStorVal]
    exact hcount
  have hcountColdPost : (sevm.currentTarget, countKey) ∉
      lengthPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_cold sevm base arrayLengthSlot countKey
      (Ne.symm hlengthFamilies.2.2) hcountCold
  have hintervalPost : lengthPost.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval := by
    rw [temporalSstorePost_other sevm indexPost arrayLengthSlot next
      sevm.currentTarget heartbeatIntervalSlot (pairNe (Ne.symm hlengthInterval))]
    rw [temporalSstorePost_other sevm arrayPost indexKey next
      sevm.currentTarget heartbeatIntervalSlot (pairNe (by
        simpa only [heartbeatIntervalSlot, indexKey, indexSlot] using
          slot_ne_of_region_ne
          (leftRegion := configRegion) (rightRegion := indexRegion)
          (left := (1 : B256)) (right := target)
          (by norm_num [configRegion]) (by norm_num [indexRegion])
          (by change (1 : Nat) < 2 ^ 252; norm_num)
          (canonicalAddress_payload_lt htargetValid.2)
          (by norm_num [configRegion, indexRegion])))]
    rw [temporalSstorePost_other sevm lengthBase arrayKey target
      sevm.currentTarget heartbeatIntervalSlot (pairNe (by
        simpa only [heartbeatIntervalSlot, arrayKey, arrayEntrySlot] using
          slot_ne_of_region_ne
          (leftRegion := configRegion) (rightRegion := arrayRegion)
          (left := (1 : B256)) (right := next)
          (by norm_num [configRegion]) (by norm_num [arrayRegion])
          (by change (1 : Nat) < 2 ^ 252; norm_num) hnextBound
          (by norm_num [configRegion, arrayRegion])))]
    rw [temporalSloadBase_getStorVal]
    exact hinterval
  have hintervalColdPost : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      lengthPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_cold sevm base arrayLengthSlot
      heartbeatIntervalSlot hlengthInterval hintervalCold
  have hexpiryPost : lengthPost.getStorVal sevm.currentTarget
      (expirySlot newPauser) = 0 := by
    have hexpiryArray := expirySlot_ne_arrayFamily hnewValid.2 hnextBound
    have hexpiryRegistry := expirySlot_ne_registryAddressFamilies
      hnewValid.2 htargetValid.2 hnewValid.2
    rw [temporalSstorePost_other sevm indexPost arrayLengthSlot next
      sevm.currentTarget (expirySlot newPauser)
      (pairNe hexpiryArray.1)]
    rw [temporalSstorePost_other sevm arrayPost indexKey next
      sevm.currentTarget (expirySlot newPauser)
      (pairNe hexpiryRegistry.2.1)]
    rw [temporalSstorePost_other sevm lengthBase arrayKey target
      sevm.currentTarget (expirySlot newPauser)
      (pairNe hexpiryArray.2)]
    rw [temporalSloadBase_getStorVal]
    exact hexpiry
  have hwarmExpiryPost : (sevm.currentTarget, expirySlot newPauser) ∈
      lengthPost.accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys,
      temporalSstorePost_accessedStorageKeys]
    exact temporalSloadBase_preserves_warm sevm base arrayLengthSlot
      (expirySlot newPauser) hwarmExpiry
  let M' := M.write (arrayLengthWord * 32).toNat next.toBytes
  let img' := Bytes.writeAt img (arrayLengthWord * 32).toNat next.toBytes
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsize' : 640 ≤ M'.size := by
    dsimp only [M']
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide +kernel]
    split
    · omega
    · decide +kernel
  have halign' : M'.size % 32 = 0 :=
    Mem.aligned_write_word halign
  have harrayLengthOff' :
      (arrayLengthWord * 32).toNat + 32 ≤ M'.size := by
    dsimp only [M']
    rw [Mem.size_write_word_at,
      show (arrayLengthWord * 32).toNat + 32 = 704 by decide +kernel]
    split
    · omega
    · decide +kernel
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
  have hprevious' : Bytes.toB256
      (img'.sliceD (previousPauserWord * 32).toNat 32 0) = 0 :=
    (sliceBefore (by decide)).trans hprevious
  have hnew' : Bytes.toB256
      (img'.sliceD (newPauserWord * 32).toNat 32 0) = newPauser :=
    (sliceBefore (by decide)).trans hnew
  have hcontinuation' : Bytes.toB256
      (img'.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (sliceBefore (by decide)).trans hcontinuation
  rcases afterOldPauser_freshNonzero_runCompiled dp sevm lengthPost M' img'
      target newPauser timestamp interval expiry count nextCount next countOriginal
      countCost G hwf' hreads' htarget' hprevious' hnew' hcontinuation'
      hnewValid hsize' halign' htime hcountPost hcountOrig hcountNext
      hcountCost hintervalPost hintervalColdPost hexpiryPost hexpiryOrig
      hwarmExpiryPost hstatic hextension hexpiryNonzero with
    ⟨post, hafter, hgas, hstoreExpiry, hlogs⟩
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
          (by simp only [Devm.gasLeft_setMach];
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hafter
  have hstoreLength : Func.RunCompiled fs sevm
      (indexPost.setMach ⟨[arrayLengthSlot, next, next], M',
        afterGas + 12 + lengthCost⟩)
      (Ninst.sstore ::: .call afterOldPauserSlot) post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hlengthIndex hlengthOrig hlengthCost
        hwarmLengthIndex (by norm_num [gCallStipend]; omega) hstatic)
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
      have hval : (M'.read (arrayLengthWord * 32).toNat 32).1.toB256 = next := by
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
        hwarmIndexArray (by norm_num [gCallStipend]; omega) hstatic)
      hlengthTail
  have htargetOff' : (targetWord * 32).toNat + 32 ≤ M'.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hlengthOff' : (arrayLengthWord * 32).toNat + 32 ≤ M'.size := by
    exact harrayLengthOff'
  have htargetMem : (M'.read (targetWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' htargetOff')]
  have hlengthMem : (M'.read (arrayLengthWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hlengthOff')]
  have htargetVal : (M'.read (targetWord * 32).toNat 32).1.toB256 =
      target := by
    rw [Mem.Reads.read hreads']
    exact htarget'
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
      rw [Devm.extCost_zero_of_le halign' hlengthOff']
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
        hwarmArrayBase (by norm_num [gCallStipend]; omega) hstatic)
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
      rw [Devm.extCost_zero_of_le halign' hlengthOff']
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
    rcases hmemoryShape with hsize640 | hsize672 | hcovered
    · have hcost : arrayLengthMemoryCost M = 6 := by
        simp only [arrayLengthMemoryCost, hsize640]
        decide +kernel
      rw [hcost]
      func_run (5) [next, 6]
      case h_ext =>
        exact Devm.extCost_of_size hsize640 (by decide +kernel)
      case a =>
        have hg : afterGas + 72 + 6 + arrayCost + indexCost + lengthCost -
            (15 + 6) =
            afterGas + 57 + arrayCost + indexCost + lengthCost := by omega
        rw [hg]
        exact harrayTail
    · have hcost : arrayLengthMemoryCost M = 3 := by
        simp only [arrayLengthMemoryCost, hsize672]
        decide +kernel
      rw [hcost]
      func_run (5) [next, 3]
      case h_ext =>
        exact Devm.extCost_of_size hsize672 (by decide +kernel)
      case a =>
        have hg : afterGas + 72 + 3 + arrayCost + indexCost + lengthCost -
            (15 + 3) =
            afterGas + 57 + arrayCost + indexCost + lengthCost := by omega
        rw [hg]
        exact harrayTail
    · have hcost : arrayLengthMemoryCost M = 0 := by
        simp only [arrayLengthMemoryCost,
          memExtSize_of_le halign hcovered, Nat.sub_self]
      rw [hcost]
      func_run (5) [next, 0]
      case h_ext =>
        exact Devm.extCost_zero_of_le halign hcovered
      case a =>
        have hg : afterGas + 72 + 0 + arrayCost + indexCost + lengthCost -
            15 = afterGas + 57 + arrayCost + indexCost + lengthCost := by omega
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
  refine ⟨post, ?_, hgas, hstoreExpiry, ?_⟩
  · simp only [appendTarget]
    func_run (1)
    case a =>
      have hg : G + 25666 + arrayLengthMemoryCost M +
            temporalSloadCost sevm base arrayLengthSlot +
            arrayCost + indexCost + lengthCost +
            temporalSloadCost sevm
              (temporalSstorePost sevm
                (temporalSstorePost sevm
                  (temporalSstorePost sevm
                    (temporalSloadBase sevm base arrayLengthSlot)
                    (arrayEntrySlot next) target)
                  (indexSlot target) next)
                arrayLengthSlot next)
              (countSlot newPauser) + countCost - 3 =
          afterGas + 72 + arrayLengthMemoryCost M +
            arrayCost + indexCost + lengthCost +
            temporalSloadCost sevm base arrayLengthSlot := by
        dsimp only [afterGas, lengthPost, indexPost, arrayPost, lengthBase,
          countKey, indexKey, arrayKey]
        omega
      rw [hg]
      exact hload
  · rw [temporalSstorePost_logs, temporalSstorePost_logs,
      temporalSstorePost_logs, temporalSloadBase_logs] at hlogs
    exact hlogs

/-- Exact fresh-kernel reserve, including actual assignment/length/count read
costs and caller-supplied exact SSTORE value-cost partitions. -/
def freshSetPauserKernelGas (sevm : Sevm) (base : Devm) (M : Mem)
    (entries : List Entry) (target newPauser : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost : Nat) : Nat :=
  let next := Nat.toB256 (entries.length + 1)
  let assigned := assignmentPost sevm base target newPauser
  25756 + arrayLengthMemoryCost M +
    temporalSloadCost sevm base (assignmentSlot target) +
    assignmentCost + temporalSloadCost sevm assigned arrayLengthSlot +
    arrayCost + indexCost + lengthCost +
    temporalSloadCost sevm
      (temporalSstorePost sevm
        (temporalSstorePost sevm
          (temporalSstorePost sevm
            (temporalSloadBase sevm assigned arrayLengthSlot)
            (arrayEntrySlot next) target)
          (indexSlot target) next)
        arrayLengthSlot next)
      (countSlot newPauser) + countCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-kernel success for a fresh target assigned to a nonzero
pauser.  The source trace and refined Registry projection are derived from the
entry witness; all concrete storage/access/value-cost facts used by the
emitted five-write path remain explicit. -/
theorem setPauserKernel_freshNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes) (entries : List Entry)
    (target newPauser timestamp interval expiry : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal
      countOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = none)
    (hwf : Mem.Wf M) (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (hsize : 640 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : sevm.benvStat.time = timestamp)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 newPauser =
      assignmentCost)
    (harray : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot newPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal
      (Nat.toB256 (assignmentCount entries newPauser))
      (Nat.toB256 (assignmentCount entries newPauser + 1)) = countCost)
    (hcountNextWord : (1 : B256) +
      Nat.toB256 (assignmentCount entries newPauser) =
      Nat.toB256 (assignmentCount entries newPauser + 1))
    (hcountCold : (sevm.currentTarget, countSlot newPauser) ∉
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hinterval : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hexpiry : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ trace post,
      setPauserSourceTrace entries target newPauser = some trace ∧
      trace.postEntries = entries ++ [(target, newPauser)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], M, G + freshSetPauserKernelGas sevm base M
          entries target newPauser assignmentCost arrayCost indexCost
          lengthCost countCost⟩)
        setPauserKernel post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, 0, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  let assignmentKey := assignmentSlot target
  let assignBase := assignmentBase sevm base target
  let assignPost := assignmentPost sevm base target newPauser
  let next := Nat.toB256 (entries.length + 1)
  let length := Nat.toB256 entries.length
  let count := Nat.toB256 (assignmentCount entries newPauser)
  let nextCount := Nat.toB256 (assignmentCount entries newPauser + 1)
  let appendGas := G + 25666 + arrayLengthMemoryCost M +
    temporalSloadCost sevm assignPost arrayLengthSlot +
    arrayCost + indexCost + lengthCost +
    temporalSloadCost sevm
      (temporalSstorePost sevm
        (temporalSstorePost sevm
          (temporalSstorePost sevm
            (temporalSloadBase sevm assignPost arrayLengthSlot)
            (arrayEntrySlot next) target)
          (indexSlot target) next)
        arrayLengthSlot next)
      (countSlot newPauser) + countCost
  have hassignment : base.getStorVal sevm.currentTarget assignmentKey = 0 := by
    change (Devm.getStor base sevm.currentTarget).get assignmentKey = 0
    simpa [logicalStorageOfStor, assignmentKey,
      findEntry_none_assignmentAt hfind] using
      hw.assignments target htargetValid.2
  have hassignmentBase : assignBase.getStorVal sevm.currentTarget
      assignmentKey = 0 := by
    simpa only [assignBase, assignmentBase,
      temporalSloadBase_getStorVal] using
      hassignment
  have hwarmAssignment : (sevm.currentTarget, assignmentKey) ∈
      assignBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm base assignmentKey
  have hlength : assignPost.getStorVal sevm.currentTarget
      arrayLengthSlot = length := by
    have hne := registryAddressFamilies_ne_arrayLengthSlot
      htargetValid.2 htargetValid.2
    change (temporalSstorePost sevm assignBase assignmentKey
      newPauser).getStorVal sevm.currentTarget arrayLengthSlot = length
    rw [temporalSstorePost_other sevm assignBase assignmentKey newPauser
      sevm.currentTarget arrayLengthSlot (by
        intro hp
        exact hne.1 (congrArg Prod.snd hp).symm)]
    change (temporalSloadBase sevm base assignmentKey).getStorVal
      sevm.currentTarget arrayLengthSlot = length
    rw [temporalSloadBase_getStorVal]
    change (Devm.getStor base sevm.currentTarget).get arrayLengthSlot = length
    simpa [logicalStorageOfStor, length] using hw.lengthWord
  have hindex : assignPost.getStorVal sevm.currentTarget
      (indexSlot target) = 0 := by
    have hne := registryAddressFamilies_pairwise
      htargetValid.2 htargetValid.2 hnewValid.2
    change (temporalSstorePost sevm assignBase assignmentKey
      newPauser).getStorVal sevm.currentTarget (indexSlot target) = 0
    rw [temporalSstorePost_other sevm assignBase assignmentKey newPauser
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
  have hcount : assignPost.getStorVal sevm.currentTarget
      (countSlot newPauser) = count := by
    have hne := registryAddressFamilies_pairwise
      htargetValid.2 htargetValid.2 hnewValid.2
    change (temporalSstorePost sevm assignBase assignmentKey
      newPauser).getStorVal sevm.currentTarget (countSlot newPauser) = count
    rw [temporalSstorePost_other sevm assignBase assignmentKey newPauser
      sevm.currentTarget (countSlot newPauser) (by
        intro hp
        exact hne.2.1 (congrArg Prod.snd hp).symm)]
    change (temporalSloadBase sevm base assignmentKey).getStorVal
      sevm.currentTarget (countSlot newPauser) = count
    rw [temporalSloadBase_getStorVal]
    change (Devm.getStor base sevm.currentTarget).get
      (countSlot newPauser) = count
    simpa [logicalStorageOfStor, count] using
      hw.counts newPauser hnewValid.2
  have hnextBound : next.toNat < 2 ^ 252 := by
    dsimp only [next]
    rw [B256.toNat_toB256_of_lt hw.fresh_length_lt_2pow256]
    exact hw.fresh_length_lt_2pow252
  have hnextNonzero : next ≠ 0 := by
    intro hz
    have := congrArg B256.toNat hz
    rw [show next = Nat.toB256 (entries.length + 1) by rfl,
      B256.toNat_toB256_of_lt hw.fresh_length_lt_2pow256] at this
    simp only [B256.toNat_zero] at this
    omega
  have hlengthNext : (1 : B256) + length = next := by
    simpa only [length, next] using hlengthNextWord
  have hcountNext : (1 : B256) + count = nextCount := by
    simpa only [count, nextCount] using hcountNextWord
  let M' := M.write (previousPauserWord * 32).toNat (0 : B256).toBytes
  let img' := Bytes.writeAt img (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  have hwf' : Mem.Wf M' := hwf.write _ _
  have hreads' : Mem.Reads M' img' := Mem.Reads.write hwf hreads _ _
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (previousPauserWord * 32).toNat + 32 ≤ M.size by
          have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by
            decide
          omega))
  have hsize' : 640 ≤ M'.size := by rw [hsizeM']; exact hsize
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
  have hmemoryShape' : M'.size = 640 ∨ M'.size = 672 ∨
      (arrayLengthWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hend : (arrayLengthWord * 32).toNat + 32 = 704 := by
      decide +kernel
    rw [hend]
    omega
  rcases appendTarget_freshNonzero_runCompiled dp sevm assignPost M' img'
      target newPauser timestamp interval expiry length next count nextCount
      arrayOriginal indexOriginal lengthOriginal countOriginal
      arrayCost indexCost lengthCost countCost G hwf' hreads' htarget'
      hprevious' hnew' hcontinuation' htargetValid hnewValid hnextBound
      hnextNonzero hsize' halign' hmemoryShape' htime hlength hlengthNext
      harray harrayOrig
      harrayCost hwarmArray hindex hindexOrig hindexCost hwarmIndex
      hlengthOrig hlengthCost hcount hcountOrig hcountNext hcountCost
      hcountCold hinterval hintervalCold hexpiry hexpiryOrig hwarmExpiry
      hstatic hextension hexpiryNonzero with
    ⟨post, happendRaw, hgas, hstoreExpiry, hlogs⟩
  have hmemoryCost : arrayLengthMemoryCost M' =
      arrayLengthMemoryCost M := by
    simp only [arrayLengthMemoryCost, hsizeM']
  have happend : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (assignPost.setMach ⟨[], M', appendGas⟩)
      appendTarget post := by
    simpa only [appendGas, hmemoryCost] using happendRaw
  have hkernelRun := setPauserKernel_append_runCompiled dp sevm base M img
    post target newPauser assignmentOriginal assignmentCost appendGas
    hwf hreads htarget hnew htargetValid hsize halign hassignment
    hassignmentOrig hassignmentCost
    (by simp only [appendGas]; norm_num [gCallStipend]; omega) hstatic
    happend
  rcases freshRegistration_sourceTrace_witness hw htargetValid hnewValid hfind with
    ⟨trace, htrace, hpostEntries, hwrites, hwpost⟩
  refine ⟨trace, post, htrace, hpostEntries, ?_, ?_, hgas,
    hstoreExpiry, ?_⟩
  · exact hwpost
  · have hg : G + freshSetPauserKernelGas sevm base M entries target
          newPauser assignmentCost arrayCost indexCost lengthCost countCost =
        appendGas + appendSetPauserKernelPrefixGas sevm base target
          assignmentCost := by
      dsimp only [freshSetPauserKernelGas, appendSetPauserKernelPrefixGas,
        appendGas, assignPost, assignBase, assignmentKey, next,
        assignmentPost, assignmentBase]
      omega
    rw [hg]
    exact hkernelRun
  · have hbaseLogs : assignPost.logs = base.logs := by
      dsimp only [assignPost, assignmentPost, assignmentBase]
      rw [temporalSstorePost_logs, temporalSloadBase_logs]
    rw [hbaseLogs] at hlogs
    exact hlogs

/-- Exact gas reserve for the production `registerPauser` body on the fresh,
nonzero path, including its canonical decoder/admin prefix and real staged
memory image. -/
def freshRegisterBodyGas (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target newPauser : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost : Nat) : Nat :=
  221 + freshSetPauserKernelGas sevm base
    (registerMemory target newPauser) entries target newPauser
    assignmentCost arrayCost indexCost lengthCost countCost

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact successful production body for a fresh nonzero registration. -/
theorem registerPauser_body_freshNonzero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target newPauser timestamp interval expiry : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal
      countOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost G : Nat)
    (hdata : sevm.data.length.toB256 <? 68 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = none)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (htime : sevm.benvStat.time = timestamp)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 newPauser =
      assignmentCost)
    (harray : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot newPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal
      (Nat.toB256 (assignmentCount entries newPauser))
      (Nat.toB256 (assignmentCount entries newPauser + 1)) = countCost)
    (hcountNextWord : (1 : B256) +
      Nat.toB256 (assignmentCount entries newPauser) =
      Nat.toB256 (assignmentCount entries newPauser + 1))
    (hcountCold : (sevm.currentTarget, countSlot newPauser) ∉
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hinterval : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hexpiry : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ trace post,
      setPauserSourceTrace entries target newPauser = some trace ∧
      trace.postEntries = entries ++ [(target, newPauser)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty,
          G + freshRegisterBodyGas sevm base entries target newPauser
            assignmentCost arrayCost indexCost lengthCost countCost⟩)
        (registerPauser dp) post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, 0, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  let M := registerMemory target newPauser
  let img := registerImage target newPauser
  rcases registerMemory_spec target newPauser with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      hpreviousRead, hcontinuationRead⟩
  have halign : M.size % 32 = 0 := by
    change (registerMemory target newPauser).size % 32 = 0
    rw [hsize]
  rcases setPauserKernel_freshNonzero_runCompiled dp sevm base M img entries
      target newPauser timestamp interval expiry assignmentOriginal
      arrayOriginal indexOriginal lengthOriginal countOriginal assignmentCost
      arrayCost indexCost lengthCost countCost G hw hfind hwf hreads
      htargetRead hnewRead hcontinuationRead htargetValid hnewValid
      (by
        change 640 ≤ (registerMemory target newPauser).size
        rw [hsize]) halign htime hassignmentOrig hassignmentCost harray harrayOrig
      harrayCost hwarmArray hindexOrig hindexCost hwarmIndex hlengthOrig
      hlengthCost hlengthNextWord hcountOrig hcountCost hcountNextWord
      hcountCold hinterval hintervalCold hexpiry hexpiryOrig hwarmExpiry
      hstatic hextension hexpiryNonzero with
    ⟨trace, post, htrace, hpostEntries, hwpost, hkernel,
      hgas, hstoreExpiry, hlogs⟩
  let fs := (runtime dp).main :: (runtime dp).aux
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
  have hstage : Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty,
        G + freshSetPauserKernelGas sevm base M entries target newPauser
          assignmentCost arrayCost indexCost lengthCost countCost + 112⟩)
      (arg 0 +++ mstoreAt targetWord +++
        arg 1 +++ mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 0 ::: mstoreAt continuationWord +++
        .call setPauserSlot) post := by
    unfold arg cdl
    func_run (15) [51, 3, 3, 3]
    -- Each extension goal takes exactly the alternative that fits it, in the
    -- order `func_run` emits them.  A `first` combinator over all four cost
    -- ~40 s here: a failed `exact` still unifies `N.size = n` against the
    -- write tower, so every goal paid for the alternatives it did not need.
    case h_ext => exact Devm.extCost_of_size (n := 0) rfl (by decide +kernel)
    case h_ext =>
      exact Devm.extCost_of_size (n := 544) (hM1Size _) (by decide +kernel)
    case h_ext =>
      exact Devm.extCost_of_size (n := 576) (hM2Size _ _) (by decide +kernel)
    case h_ext =>
      exact Devm.extCost_of_size (n := 608) (hM3Size _ _) (by decide +kernel)
    case h_body =>
      rw [hargTarget, hargNew]
      change Func.RunCompiled fs sevm
        (base.setMach ⟨[], M,
          G + freshSetPauserKernelGas sevm base M entries target newPauser
            assignmentCost arrayCost indexCost lengthCost countCost⟩)
        setPauserKernel post
      simpa only [fs] using hkernel
  refine ⟨trace, post, htrace, hpostEntries, hwpost, ?_, hgas,
    hstoreExpiry, hlogs⟩
  have htargetMask := canonicalAddress_mask_zero htargetValid.2
  have hnewMask := canonicalAddress_mask_zero hnewValid.2
  unfold registerPauser requireStaticArgs canonicalAddressArg onlyAdmin arg cdl
    checkNonAddress pushAddressMask pushDeployWord
  func_run (24) [0, ~~~(0 : B256), addressMask, 0,
    ~~~(0 : B256), addressMask, 0, 1]
  all_goals try { rw [hargTarget]; exact htargetMask }
  all_goals try { rw [hargNew]; exact hnewMask }
  all_goals try { simp [hadmin, B256.eqCheck] }
  all_goals first
    | (simp only [Devm.gasLeft_setMach, freshRegisterBodyGas]
       norm_num [gBase, gVerylow, gHigh, gMid, gJumpdest]
       omega)
    | skip
  case h_arm =>
    simp only [freshRegisterBodyGas]
    have hg : G + (221 + freshSetPauserKernelGas sevm base M entries
          target newPauser assignmentCost arrayCost indexCost lengthCost
          countCost) - 109 =
        G + freshSetPauserKernelGas sevm base M entries target newPauser
          assignmentCost arrayCost indexCost lengthCost countCost + 112 := by
      omega
    rw [hg]
    simpa only [arg, cdl, M, fs] using hstage

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact generated-runtime success for a fresh nonzero registration. -/
theorem registerPauser_runCompiledTo_freshNonzero
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target newPauser timestamp interval expiry : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal
      countOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost G : Nat)
    (hdata : sevm.data.length.toB256 = 68)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "registerPauser" [.address, .address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (hargTarget : Sevm.dataWord sevm (32 * 0 + 4) = target)
    (hargNew : Sevm.dataWord sevm (32 * 1 + 4) = newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hfind : findEntry entries target = none)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (htime : sevm.benvStat.time = timestamp)
    (hassignmentOrig : getOrigStorVal sevm sevm.currentTarget
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 newPauser =
      assignmentCost)
    (harray : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hcountOrig : getOrigStorVal sevm sevm.currentTarget
      (countSlot newPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal
      (Nat.toB256 (assignmentCount entries newPauser))
      (Nat.toB256 (assignmentCount entries newPauser + 1)) = countCost)
    (hcountNextWord : (1 : B256) +
      Nat.toB256 (assignmentCount entries newPauser) =
      Nat.toB256 (assignmentCount entries newPauser + 1))
    (hcountCold : (sevm.currentTarget, countSlot newPauser) ∉
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hinterval : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hexpiry : (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (assignmentPost sevm base target newPauser).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0) :
    ∃ trace post,
      setPauserSourceTrace entries target newPauser = some trace ∧
      trace.postEntries = entries ++ [(target, newPauser)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor base sevm.currentTarget) trace.writes))
        trace.postEntries ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + registerPauserDispatchGas +
            freshRegisterBodyGas sevm base entries target newPauser
              assignmentCost arrayCost indexCost lengthCost countCost⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, 0, newPauser], []⟩,
         ⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 68 = 0 := by
    rw [hdata]
    decide +kernel
  rcases registerPauser_body_freshNonzero_runCompiled dp sevm base entries
      target newPauser timestamp interval expiry assignmentOriginal
      arrayOriginal indexOriginal lengthOriginal countOriginal assignmentCost
      arrayCost indexCost lengthCost countCost G hbodyData hadmin hargTarget
      hargNew hw hfind htargetValid hnewValid htime hassignmentOrig
      hassignmentCost harray harrayOrig harrayCost hwarmArray hindexOrig
      hindexCost hwarmIndex hlengthOrig hlengthCost hlengthNextWord hcountOrig
      hcountCost hcountNextWord hcountCold hinterval hintervalCold hexpiry
      hexpiryOrig hwarmExpiry hstatic hextension hexpiryNonzero with
    ⟨trace, post, htrace, hpostEntries, hwpost, hbody, hgas,
      hstoreExpiry, hlogs⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases registerPauser_dispatch_runCompiledTo dp sevm base
      (freshRegisterBodyGas sevm base entries target newPauser
        assignmentCost arrayCost indexCost lengthCost countCost)
      G (.ok post) hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas,
    hstoreExpiry, hlogs, hcompile⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Exact clean direct-message effects for a fresh nonzero registration,
derived from the generated-runtime execution rather than supplied as facts
about the raw result. -/
theorem registerPauser_freshNonzero_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr}
    {final settled : Devm}
    (entries : List Entry) (target newPauser timestamp interval expiry : B256)
    (assignmentOriginal arrayOriginal indexOriginal lengthOriginal
      countOriginal : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost G : Nat)
    (htargetOwner : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target newPauser)
    (hgasEntry : msg.gas = G + registerPauserDispatchGas +
      freshRegisterBodyGas (initSevm msg) (initDevm msg) entries target
        newPauser assignmentCost arrayCost indexCost lengthCost countCost)
    (hadmin : msg.caller.toB256 = dp.admin)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor (initDevm msg) ca)) entries)
    (hfind : findEntry entries target = none)
    (htargetValid : nonzeroCanonicalAddress target)
    (hnewValid : nonzeroCanonicalAddress newPauser)
    (htime : (initSevm msg).benvStat.time = timestamp)
    (hassignmentOrig : getOrigStorVal (initSevm msg) ca
      (assignmentSlot target) = assignmentOriginal)
    (hassignmentCost : sstoreValueCost assignmentOriginal 0 newPauser =
      assignmentCost)
    (harray : (assignmentPost (initSevm msg) (initDevm msg)
      target newPauser).getStorVal ca
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (ca,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (assignmentPost (initSevm msg) (initDevm msg)
          target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (ca, indexSlot target) ∈
      (assignmentPost (initSevm msg) (initDevm msg)
        target newPauser).accessedStorageKeys)
    (hlengthOrig : getOrigStorVal (initSevm msg) ca arrayLengthSlot =
      lengthOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal
      (Nat.toB256 entries.length) (Nat.toB256 (entries.length + 1)) =
        lengthCost)
    (hlengthNextWord : (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 (entries.length + 1))
    (hcountOrig : getOrigStorVal (initSevm msg) ca
      (countSlot newPauser) = countOriginal)
    (hcountCost : sstoreValueCost countOriginal
      (Nat.toB256 (assignmentCount entries newPauser))
      (Nat.toB256 (assignmentCount entries newPauser + 1)) = countCost)
    (hcountNextWord : (1 : B256) +
      Nat.toB256 (assignmentCount entries newPauser) =
      Nat.toB256 (assignmentCount entries newPauser + 1))
    (hcountCold : (ca, countSlot newPauser) ∉
      (assignmentPost (initSevm msg) (initDevm msg)
        target newPauser).accessedStorageKeys)
    (hinterval : (assignmentPost (initSevm msg) (initDevm msg)
      target newPauser).getStorVal ca heartbeatIntervalSlot = interval)
    (hintervalCold : (ca, heartbeatIntervalSlot) ∉
      (assignmentPost (initSevm msg) (initDevm msg)
        target newPauser).accessedStorageKeys)
    (hexpiry : (assignmentPost (initSevm msg) (initDevm msg)
      target newPauser).getStorVal ca (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal (initSevm msg) ca
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (ca, expirySlot newPauser) ∈
      (assignmentPost (initSevm msg) (initDevm msg)
        target newPauser).accessedStorageKeys)
    (hstatic : (initSevm msg).isStatic = false)
    (hextension : CheckedHeartbeatExtension timestamp interval expiry)
    (hexpiryNonzero : expiry ≠ 0)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    ∃ trace,
      setPauserSourceTrace entries target newPauser = some trace ∧
      trace.postEntries = entries ++ [(target, newPauser)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor (initDevm msg) ca) trace.writes))
        trace.postEntries ∧
      settled.gasLeft = G ∧
      settled.getStorVal ca (expirySlot newPauser) = expiry ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [pauserSetEvent, target, 0, newPauser], []⟩,
         ⟨ca, [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  have hdataInit : (initSevm msg).data =
      registerPauserCalldata target newPauser := by
    simpa [initSevm] using hdata
  rcases registerPauserCalldata_spec (initSevm msg) target newPauser hdataInit with
    ⟨hdataLengthRaw, hselectorRaw, hargTargetRaw, hargNewRaw⟩
  have hdataLength : (initSevm msg).data.length.toB256 = 68 :=
    hdataLengthRaw
  have hselector : Sevm.selector (initSevm msg) =
      selector "registerPauser" [.address, .address] := hselectorRaw
  have hargTarget : Sevm.dataWord (initSevm msg) (32 * 0 + 4) = target := by
    exact hargTargetRaw
  have hargNew : Sevm.dataWord (initSevm msg) (32 * 1 + 4) = newPauser := by
    exact hargNewRaw
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
  rcases registerPauser_runCompiledTo_freshNonzero dp (initSevm msg)
      (initDevm msg) entries target newPauser timestamp interval expiry
      assignmentOriginal arrayOriginal indexOriginal lengthOriginal
      countOriginal assignmentCost arrayCost indexCost lengthCost countCost G
      hdataLength hvalueInit hselector hcodeAddressInit hcodeInit hadminInit
      hargTarget hargNew (by simpa [hownerInit] using hw) hfind htargetValid
      hnewValid htime (by simpa [hownerInit] using hassignmentOrig)
      hassignmentCost (by simpa [hownerInit] using harray)
      (by simpa [hownerInit] using harrayOrig) harrayCost
      (by simpa [hownerInit] using hwarmArray)
      (by simpa [hownerInit] using hindexOrig) hindexCost
      (by simpa [hownerInit] using hwarmIndex)
      (by simpa [hownerInit] using hlengthOrig) hlengthCost hlengthNextWord
      (by simpa [hownerInit] using hcountOrig) hcountCost hcountNextWord
      (by simpa [hownerInit] using hcountCold)
      (by simpa [hownerInit] using hinterval)
      (by simpa [hownerInit] using hintervalCold)
      (by simpa [hownerInit] using hexpiry)
      (by simpa [hownerInit] using hexpiryOrig)
      (by simpa [hownerInit] using hwarmExpiry) hstatic hextension
      hexpiryNonzero with
    ⟨trace, post, htrace, hpostEntries, hwpost, hrun, hgas,
      hstoreExpiry, hlogs, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + registerPauserDispatchGas +
          freshRegisterBodyGas (initSevm msg) (initDevm msg) entries target
            newPauser assignmentCost arrayCost indexCost lengthCost countCost⟩ =
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
  · simpa [hownerInit] using hstoreExpiry
  · simpa [hownerInit] using hlogs

end Blanc.LidoCircuitBreaker
