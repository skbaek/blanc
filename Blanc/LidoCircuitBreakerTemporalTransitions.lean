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

private theorem accessedStorageKeys_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedStorageKeys = base.accessedStorageKeys := rfl

private theorem refundCounter_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).refundCounter = base.refundCounter := rfl

private def temporalSloadBase (sevm : Sevm) (base : Devm)
    (key : B256) : Devm :=
  if (sevm.currentTarget, key) ∈ base.accessedStorageKeys then base
  else addAccessedStorageKey base sevm.currentTarget key

private def temporalSloadCost (sevm : Sevm) (base : Devm)
    (key : B256) : Nat :=
  if (sevm.currentTarget, key) ∈ base.accessedStorageKeys then gasWarmAccess
  else gasColdSload

private def temporalSstorePost (sevm : Sevm) (base : Devm)
    (key value : B256) : Devm :=
  (base.withRefundCounter (sstoreNewRefundCounter value
    (getOrigStorVal sevm sevm.currentTarget key)
    (base.getStorVal sevm.currentTarget key) base.refundCounter)).setStorVal
      sevm.currentTarget key value

private theorem temporal_sload_runCompiled
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

private theorem temporal_sstore_runCompiled
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

private theorem temporalSloadBase_warm
    (sevm : Sevm) (base : Devm) (key : B256) :
    (sevm.currentTarget, key) ∈
      (temporalSloadBase sevm base key).accessedStorageKeys := by
  unfold temporalSloadBase
  split <;> rename_i h
  · exact h
  · exact Std.HashSet.mem_insert_self

private theorem temporalSloadBase_getStorVal
    (sevm : Sevm) (base : Devm) (readKey : B256)
    (a : Adr) (key : B256) :
    (temporalSloadBase sevm base readKey).getStorVal a key =
      base.getStorVal a key := by
  unfold temporalSloadBase
  split <;> rfl

private theorem temporalSloadBase_preserves_warm
    (sevm : Sevm) (base : Devm) (readKey key : B256)
    (h : (sevm.currentTarget, key) ∈ base.accessedStorageKeys) :
    (sevm.currentTarget, key) ∈
      (temporalSloadBase sevm base readKey).accessedStorageKeys := by
  unfold temporalSloadBase
  split
  · exact h
  · exact Std.HashSet.mem_insert.mpr (Or.inr h)

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

private theorem temporalSloadBase_logs
    (sevm : Sevm) (base : Devm) (key : B256) :
    (temporalSloadBase sevm base key).logs = base.logs := by
  unfold temporalSloadBase
  split <;> rfl

private theorem temporalSstorePost_other
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

private theorem temporalSstorePost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).accessedStorageKeys =
      base.accessedStorageKeys := rfl

private theorem temporalSstorePost_logs
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).logs = base.logs := rfl

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
        (base.setMach ⟨[carry], M, G + 23592⟩)
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
      (eventBase.setMach ⟨[carry], M, G + 23604⟩)
      (.call registerAfterSetSlot) post := by
    apply Func.RunCompiled.call hlookup
      (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := eventBase.setMach ⟨[carry], M, G + 23604⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G + 23592)
          (by simp only [Devm.gasLeft_setMach];
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hregister
  have hbranch : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨[1, carry], M, G + 23618⟩)
      ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot)) post := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := eventBase.setMach ⟨[1, carry], M, G + 23618⟩)
          (x := (1 : B256)) (s := [carry])
          (cost := gVerylow + gHigh + gJumpdest) (G := G + 23604)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]))
    · exact hcall
  have hcontinuationRun : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨[carry], M, G + 23627⟩)
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
    (hsize : 768 ≤ M.size)
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
  have hcountBase : countBase.getStorVal sevm.currentTarget countKey = count := by
    simpa only [countBase, countKey, temporalSloadBase_getStorVal] using hcount
  have hwarmCount : (sevm.currentTarget, countKey) ∈
      countBase.accessedStorageKeys := by
    exact temporalSloadBase_warm sevm base countKey
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
  let fs := (runtime dp).main :: (runtime dp).aux
  have hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser := by
    simp [fs, runtime, aux, finishSetPauserSlot]
  have hfinishCall : Func.RunCompiled fs sevm
      (countPost.setMach ⟨[carry], M, G + 25539⟩)
      (.call finishSetPauserSlot) post := by
    apply Func.RunCompiled.call hfinishLookup
      (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := countPost.setMach ⟨[carry], M, G + 25539⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G + 25527)
          (by simp only [Devm.gasLeft_setMach];
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hfinish
  have hstoreCount : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[countKey, nextCount, carry], M,
        G + 25539 + countCost⟩)
      (Ninst.sstore ::: .call finishSetPauserSlot) post := by
    apply Func.RunCompiled.next
    · exact temporal_sstore_runCompiled hcountBase hcountOrig hcountCost
        hwarmCount (by norm_num [gCallStipend]; omega) hstatic
    · exact hfinishCall
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewMemory : (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = newPauser := by
    rw [Mem.Reads.read hreads]
    exact hnew
  have hcountKeyTail : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[nextCount, carry], M, G + 25551 + countCost⟩)
      (newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot) post := by
    func_run (4) [3, countKey]
    all_goals try {
      simpa [countKey, countSlot, slot] using
        congrArg (fun x : B256 => (regionWord countRegion).or x) hnewValue }
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow]
    case a =>
      rw [hnewMemory]
      have hg : G + 25551 + countCost - 12 = G + 25539 + countCost := by
        omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (countBase.setMach ⟨[countKey, nextCount, carry], M,
          G + 25539 + countCost⟩)
        (Ninst.sstore ::: .call finishSetPauserSlot) post
      exact hstoreCount
  have hcountTail : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[count, carry], M,
        G + 25557 + countCost⟩)
      (pushB256 1 ::: add ::: newCountKey +++
        Ninst.sstore ::: .call finishSetPauserSlot) post := by
    func_run (2)
    case a =>
      simp only
      rw [hcountNext]
      have hg : G + 25557 + countCost - 6 = G + 25551 + countCost := by
        omega
      rw [hg]
      exact hcountKeyTail
  have hcountLoad : Func.RunCompiled fs sevm
      (base.setMach ⟨[countKey, carry], M,
        G + 25557 + countCost + temporalSloadCost sevm base countKey⟩)
      (Ninst.sload ::: pushB256 1 ::: add ::: newCountKey +++
        Ninst.sstore ::: .call finishSetPauserSlot) post := by
    exact Func.RunCompiled.next (temporal_sload_runCompiled hcount (by
      simp only [List.length_cons, List.length_nil]
      decide))
      hcountTail
  have hcountBody : Func.RunCompiled fs sevm
      (base.setMach ⟨[carry], M,
        G + 25569 + temporalSloadCost sevm base countKey + countCost⟩)
      (newCountKey +++ Ninst.sload ::: pushB256 1 ::: add :::
        newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot) post := by
    func_run (4) [3, countKey]
    all_goals try {
      simpa [countKey, countSlot, slot] using
        congrArg (fun x : B256 => (regionWord countRegion).or x) hnewValue }
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow]
    case a =>
      rw [hnewMemory]
      have hg : G + 25569 + temporalSloadCost sevm base countKey +
          countCost - 12 =
          G + 25557 + countCost + temporalSloadCost sevm base countKey := by
        omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (base.setMach ⟨[countKey, carry], M,
          G + 25557 + countCost + temporalSloadCost sevm base countKey⟩)
        (Ninst.sload ::: pushB256 1 ::: add ::: newCountKey +++
          Ninst.sstore ::: .call finishSetPauserSlot) post
      exact hcountLoad
  have hbranch : Func.RunCompiled fs sevm
      (base.setMach ⟨[0, carry], M,
        G + 25582 + temporalSloadCost sevm base countKey + countCost⟩)
      ((.call removeTargetSlot) <?>
        (newCountKey +++ Ninst.sload ::: pushB256 1 ::: add :::
          newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot)) post := by
    apply Func.RunCompiled.zero
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := base.setMach ⟨[0, carry], M,
            G + 25582 + temporalSloadCost sevm base countKey + countCost⟩)
          (x := (0 : B256)) (s := [carry])
          (cost := gVerylow + gHigh)
          (G := G + 25569 + temporalSloadCost sevm base countKey + countCost)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh]
            omega))
    · exact hcountBody
  refine ⟨post, ?_, hgas, hstoreExpiry, ?_⟩
  · simp only [afterOldPauser]
    func_run (3) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow]
    case a =>
      have hnewMemory : (M.read (newPauserWord * 32).toNat 32).2 = M := by
        rw [Mem.read_snd_eq_self (memExtSize_of_le halign (by
          have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
          omega))]
      rw [Mem.Reads.read hreads, hnew, hnewMemory]
      simp only [B256.eqCheck, if_neg hnewValid.1]
      have hg : G + 25591 + temporalSloadCost sevm base countKey +
          countCost - 9 =
          G + 25582 + temporalSloadCost sevm base countKey + countCost := by
        omega
      rw [hg]
      exact hbranch
  · rw [temporalSstorePost_logs, temporalSloadBase_logs] at hlogs
    exact hlogs

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
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
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
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
          G + 25666 + temporalSloadCost sevm base arrayLengthSlot +
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
  have hsizeM' : M'.size = M.size := by
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using (show
        (arrayLengthWord * 32).toNat + 32 ≤ M.size by
          have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 768 := by decide
          omega))
  have hsize' : 768 ≤ M'.size := by rw [hsizeM']; exact hsize
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
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
      rw [Devm.extCost_zero_of_le halign' (by
        rw [hsizeM']
        have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case a =>
      have hmem : (M'.read (arrayLengthWord * 32).toNat 32).2 = M' := by
        rw [Mem.read_snd_eq_self (memExtSize_of_le halign' (by
          rw [hsizeM']
          have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 768 := by decide
          omega))]
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
    rw [hsizeM']
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hlengthOff' : (arrayLengthWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 768 := by decide
    omega
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
        afterGas + 72 + arrayCost + indexCost + lengthCost⟩)
      (pushB256 1 ::: add ::: dup 0 ::: mstoreAt arrayLengthWord +++
        loadWord targetWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    func_run (5) [next, 0]
    case h_ext =>
      have hlengthOff : (arrayLengthWord * 32).toNat + 32 ≤ M.size := by
        have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 768 := by decide
        omega
      rw [Devm.extCost_zero_of_le halign hlengthOff]
    case a =>
      have hg : afterGas + 72 + arrayCost + indexCost + lengthCost - 15 =
          afterGas + 57 + arrayCost + indexCost + lengthCost := by omega
      rw [hg]
      exact harrayTail
  have hload : Func.RunCompiled fs sevm
      (base.setMach ⟨[arrayLengthSlot], M,
        afterGas + 72 + arrayCost + indexCost + lengthCost +
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
      have hg : G + 25666 + temporalSloadCost sevm base arrayLengthSlot +
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
          afterGas + 72 + arrayCost + indexCost + lengthCost +
            temporalSloadCost sevm base arrayLengthSlot := by
        dsimp only [afterGas, lengthPost, indexPost, arrayPost, lengthBase,
          countKey, indexKey, arrayKey]
        omega
      rw [hg]
      exact hload
  · rw [temporalSstorePost_logs, temporalSstorePost_logs,
      temporalSstorePost_logs, temporalSloadBase_logs] at hlogs
    exact hlogs

end Blanc.LidoCircuitBreaker
