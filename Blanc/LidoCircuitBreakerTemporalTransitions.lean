import Blanc.LidoCircuitBreakerAccess

/-!
Exact compiled temporal transitions for the Lido CircuitBreaker runtime.

This acyclic proof leaf extends the compiled access surface with stable
registration effects.  The executable contract and inherited Registry proofs
remain unchanged.
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

private theorem addAccessedStorageKey_setMach_setMach
    {base : Devm} {target : Adr} {key : B256} {m m' : Mach} :
    (addAccessedStorageKey (base.setMach m) target key).setMach m' =
      (addAccessedStorageKey base target key).setMach m' := rfl

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
    (M : Mem) (img : Bytes) (newPauser expiry : B256) (G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hsize : 768 ≤ M.size)
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
        (base.setMach ⟨[expirySlot newPauser, expiry],
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
  have hsize' : 768 ≤ M'.size := by rw [hsizeM']; exact hsize
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have hnewCovered' :
      (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
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
    ⟨[expirySlot newPauser, expiry], M', G + 21395⟩
  let rc := sstoreNewRefundCounter expiry 0 0 base.refundCounter
  let inter := ((pre.withRefundCounter rc).setStorVal
      sevm.currentTarget (expirySlot newPauser) expiry).setMach
      ⟨[], M', G + 1395⟩
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
        change ([] : List B256).length < 1024
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
    (M : Mem) (img : Bytes) (newPauser timestamp interval expiry : B256)
    (G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hnewNonzero : newPauser ≠ 0)
    (hsize : 768 ≤ M.size)
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
        (base.setMach ⟨[], M, G + 23592⟩)
        registerAfterSet post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget (expirySlot newPauser) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, newPauser], expiry.toBytes⟩] := by
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
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
      M img newPauser expiry G hwf hreads hnew hsize halign
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
    (M : Mem) (img : Bytes) (target newPauser timestamp interval expiry : B256)
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
    (hsize : 768 ≤ M.size)
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
        (base.setMach ⟨[], M, G + 25527⟩) finishSetPauser post ∧
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
      newPauser timestamp interval expiry G hwf hreads hprevious hnew
      hnewNonzero hsize halign htime hintervalEvent hintervalColdEvent
      hexpiryEvent hexpiryOrig hwarmExpiryEvent hstatic hextension
      hexpiryNonzero with ⟨post, hregister, hgas, hstore, hlogs⟩
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hcontinuationCovered :
      (continuationWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (continuationWord * 32).toNat + 32 ≤ 768 := by decide
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
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0 := by
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
      (eventBase.setMach ⟨[], M, G + 23604⟩)
      (.call registerAfterSetSlot) post := by
    apply Func.RunCompiled.call hlookup
      (by simp only [Devm.stack_setMach, List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := eventBase.setMach ⟨[], M, G + 23604⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G + 23592)
          (by simp only [Devm.gasLeft_setMach];
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hregister
  have hbranch : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨[1], M, G + 23618⟩)
      ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot)) post := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := eventBase.setMach ⟨[1], M, G + 23618⟩)
          (x := (1 : B256)) (s := [])
          (cost := gVerylow + gHigh + gJumpdest) (G := G + 23604)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]))
    · exact hcall
  have hcontinuationRun : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨[], M, G + 23627⟩)
      (loadWord continuationWord +++ Ninst.iszero :::
        ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))) post := by
    func_run (3) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hcontinuationCovered]
      norm_num [gVerylow]
    case a =>
      rw [hcontinuationValue, hcontinuationMemory]
      norm_num
      exact hbranch
  refine ⟨post, ?_, hgas, hstore, ?_⟩
  · simp only [finishSetPauser]
    func_run (10) [3, 3, 3, 1875]
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
  · have heventLogs : eventBase.logs = base.logs ++ [eventLog] := rfl
    rw [heventLogs] at hlogs
    simpa [eventLog, List.append_assoc] using hlogs

end Blanc.LidoCircuitBreaker
