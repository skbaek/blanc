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

private theorem Bytes.sliceD_writeAt_after
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

private theorem temporalSstorePost_self
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).getStorVal
      sevm.currentTarget key = value := by
  simp [temporalSstorePost, Devm.getStorVal, Devm.getAcct,
    Devm.setStorVal, Devm.withState, Devm.setWorld, State.setStorVal,
    Devm.state, State.get_set_self, Stor.get_set_self]

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
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
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
          have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
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
private def freshArrayLengthMemoryCost (M : Mem) : Nat :=
  calculateMemoryGasCost
      (memExtSize M.size (arrayLengthWord * 32).toNat 32) -
    calculateMemoryGasCost M.size

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
          G + 25666 + freshArrayLengthMemoryCost M +
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
        afterGas + 72 + freshArrayLengthMemoryCost M +
          arrayCost + indexCost + lengthCost⟩)
      (pushB256 1 ::: add ::: dup 0 ::: mstoreAt arrayLengthWord +++
        loadWord targetWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        Ninst.sstore ::: .call afterOldPauserSlot) post := by
    rcases hmemoryShape with hsize640 | hsize672 | hcovered
    · have hcost : freshArrayLengthMemoryCost M = 6 := by
        simp only [freshArrayLengthMemoryCost, hsize640]
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
    · have hcost : freshArrayLengthMemoryCost M = 3 := by
        simp only [freshArrayLengthMemoryCost, hsize672]
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
    · have hcost : freshArrayLengthMemoryCost M = 0 := by
        simp only [freshArrayLengthMemoryCost,
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
        afterGas + 72 + freshArrayLengthMemoryCost M +
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
      have hg : G + 25666 + freshArrayLengthMemoryCost M +
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
          afterGas + 72 + freshArrayLengthMemoryCost M +
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

/-- State after the fresh path has read and replaced the target assignment. -/
def freshAssignmentBase (sevm : Sevm) (base : Devm) (target : B256) : Devm :=
  temporalSloadBase sevm base (assignmentSlot target)

def freshAssignmentPost (sevm : Sevm) (base : Devm)
    (target newPauser : B256) : Devm :=
  temporalSstorePost sevm (freshAssignmentBase sevm base target)
    (assignmentSlot target) newPauser

/-- Exact fresh-kernel reserve, including actual assignment/length/count read
costs and caller-supplied exact SSTORE value-cost partitions. -/
def freshSetPauserKernelGas (sevm : Sevm) (base : Devm) (M : Mem)
    (entries : List Entry) (target newPauser : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost : Nat) : Nat :=
  let next := Nat.toB256 (entries.length + 1)
  let assigned := freshAssignmentPost sevm base target newPauser
  25756 + freshArrayLengthMemoryCost M +
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

private theorem newPauserWord_prepend_runCompiled
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

private theorem targetKey_prepend_runCompiled
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

private theorem targetWord_prepend_runCompiled
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
    (harray : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
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
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hinterval : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hexpiry : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
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
  let assignmentBase := freshAssignmentBase sevm base target
  let assignmentPost := freshAssignmentPost sevm base target newPauser
  let next := Nat.toB256 (entries.length + 1)
  let length := Nat.toB256 entries.length
  let count := Nat.toB256 (assignmentCount entries newPauser)
  let nextCount := Nat.toB256 (assignmentCount entries newPauser + 1)
  let appendGas := G + 25666 + freshArrayLengthMemoryCost M +
    temporalSloadCost sevm assignmentPost arrayLengthSlot +
    arrayCost + indexCost + lengthCost +
    temporalSloadCost sevm
      (temporalSstorePost sevm
        (temporalSstorePost sevm
          (temporalSstorePost sevm
            (temporalSloadBase sevm assignmentPost arrayLengthSlot)
            (arrayEntrySlot next) target)
          (indexSlot target) next)
        arrayLengthSlot next)
      (countSlot newPauser) + countCost
  have hassignment : base.getStorVal sevm.currentTarget assignmentKey = 0 := by
    change (Devm.getStor base sevm.currentTarget).get assignmentKey = 0
    simpa [logicalStorageOfStor, assignmentKey,
      findEntry_none_assignmentAt hfind] using
      hw.assignments target htargetValid.2
  have hassignmentBase : assignmentBase.getStorVal sevm.currentTarget
      assignmentKey = 0 := by
    simpa only [assignmentBase, freshAssignmentBase,
      temporalSloadBase_getStorVal] using
      hassignment
  have hwarmAssignment : (sevm.currentTarget, assignmentKey) ∈
      assignmentBase.accessedStorageKeys :=
    temporalSloadBase_warm sevm base assignmentKey
  have hlength : assignmentPost.getStorVal sevm.currentTarget
      arrayLengthSlot = length := by
    have hne := registryAddressFamilies_ne_arrayLengthSlot
      htargetValid.2 htargetValid.2
    change (temporalSstorePost sevm assignmentBase assignmentKey
      newPauser).getStorVal sevm.currentTarget arrayLengthSlot = length
    rw [temporalSstorePost_other sevm assignmentBase assignmentKey newPauser
      sevm.currentTarget arrayLengthSlot (by
        intro hp
        exact hne.1 (congrArg Prod.snd hp).symm)]
    change (temporalSloadBase sevm base assignmentKey).getStorVal
      sevm.currentTarget arrayLengthSlot = length
    rw [temporalSloadBase_getStorVal]
    change (Devm.getStor base sevm.currentTarget).get arrayLengthSlot = length
    simpa [logicalStorageOfStor, length] using hw.lengthWord
  have hindex : assignmentPost.getStorVal sevm.currentTarget
      (indexSlot target) = 0 := by
    have hne := registryAddressFamilies_pairwise
      htargetValid.2 htargetValid.2 hnewValid.2
    change (temporalSstorePost sevm assignmentBase assignmentKey
      newPauser).getStorVal sevm.currentTarget (indexSlot target) = 0
    rw [temporalSstorePost_other sevm assignmentBase assignmentKey newPauser
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
  have hcount : assignmentPost.getStorVal sevm.currentTarget
      (countSlot newPauser) = count := by
    have hne := registryAddressFamilies_pairwise
      htargetValid.2 htargetValid.2 hnewValid.2
    change (temporalSstorePost sevm assignmentBase assignmentKey
      newPauser).getStorVal sevm.currentTarget (countSlot newPauser) = count
    rw [temporalSstorePost_other sevm assignmentBase assignmentKey newPauser
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
  rcases appendTarget_freshNonzero_runCompiled dp sevm assignmentPost M' img'
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
  have hmemoryCost : freshArrayLengthMemoryCost M' =
      freshArrayLengthMemoryCost M := by
    simp only [freshArrayLengthMemoryCost, hsizeM']
  have happend : Func.RunCompiled
      ((runtime dp).main :: (runtime dp).aux) sevm
      (assignmentPost.setMach ⟨[], M', appendGas⟩)
      appendTarget post := by
    simpa only [appendGas, hmemoryCost] using happendRaw
  let fs := (runtime dp).main :: (runtime dp).aux
  have happendLookup : fs[appendTargetSlot]? = some appendTarget := by
    simp [fs, runtime, aux, appendTargetSlot]
  have happendCall : Func.RunCompiled fs sevm
      (assignmentPost.setMach ⟨[], M', appendGas + 12⟩)
      (.call appendTargetSlot) post := by
    apply Func.RunCompiled.call happendLookup (by
      simp only [Devm.stack_setMach, List.length_nil]
      decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := assignmentPost.setMach ⟨[], M', appendGas + 12⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := appendGas)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]))
    · simpa only [appendGas] using happend
  have hbranch : Func.RunCompiled fs sevm
      (assignmentPost.setMach ⟨[1], M', appendGas + 26⟩)
      ((.call appendTargetSlot) <?>
        (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot))
      post := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide) (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := assignmentPost.setMach ⟨[1], M', appendGas + 26⟩)
          (x := (1 : B256)) (s := [])
          (cost := gVerylow + gHigh + gJumpdest) (G := appendGas + 12)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]))
    · exact happendCall
  have hiszero : Func.RunCompiled fs sevm
      (assignmentPost.setMach ⟨[0], M', appendGas + 29⟩)
      (Ninst.iszero ::: ((.call appendTargetSlot) <?>
        (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    func_run (1) [1]
    case a => exact hbranch
  have hstore : Func.RunCompiled fs sevm
      (assignmentBase.setMach
        ⟨[assignmentKey, newPauser, 0], M',
          appendGas + 29 + assignmentCost⟩)
      (Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hassignmentBase hassignmentOrig
        hassignmentCost hwarmAssignment (by norm_num [gCallStipend]; omega)
        hstatic)
      hiszero
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have hnewCovered' : (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 640 := by decide
    omega
  have htargetMemory : (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have htargetCovered' : (targetWord * 32).toNat + 32 ≤ M'.size := by
    rw [hsizeM']
    exact htargetCovered
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
  have htargetKeySecond : Func.RunCompiled fs sevm
      (assignmentBase.setMach ⟨[newPauser, 0], M',
        appendGas + 41 + assignmentCost⟩)
      (targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    simp only [assignmentKey] at hstore
    have hrun := targetKey_prepend_runCompiled htargetValue' htargetMemory'
      halign' htargetCovered' (by simp) hstore
    have hg : appendGas + 29 + assignmentCost + 12 =
        appendGas + 41 + assignmentCost := by omega
    rw [hg] at hrun
    exact hrun
  have hnewTail : Func.RunCompiled fs sevm
      (assignmentBase.setMach ⟨[0], M', appendGas + 47 + assignmentCost⟩)
      (loadWord newPauserWord +++ targetKey +++ Ninst.sstore :::
        Ninst.iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    have hrun := newPauserWord_prepend_runCompiled hnewValue' hnewMemory'
      halign' hnewCovered' (by simp) htargetKeySecond
    have hg : appendGas + 41 + assignmentCost + 6 =
        appendGas + 47 + assignmentCost := by omega
    rw [hg] at hrun
    exact hrun
  have hsavePrevious : Func.RunCompiled fs sevm
      (assignmentBase.setMach ⟨[0, 0], M,
        appendGas + 53 + assignmentCost⟩)
      (mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    func_run (2) [0]
    case h_ext =>
      rw [Devm.extCost_zero_of_le halign (by
        have hoff : (previousPauserWord * 32).toNat + 32 ≤ 640 := by decide
        omega)]
    case a =>
      have hg : appendGas + 53 + assignmentCost - 6 =
          appendGas + 47 + assignmentCost := by omega
      rw [hg]
      change Func.RunCompiled fs sevm
        (assignmentBase.setMach ⟨[0], M', appendGas + 47 + assignmentCost⟩)
        _ post
      exact hnewTail
  have hdup : Func.RunCompiled fs sevm
      (assignmentBase.setMach ⟨[0], M, appendGas + 56 + assignmentCost⟩)
      (dup 0 ::: mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    func_run (1)
    case a =>
      have hg : appendGas + 56 + assignmentCost - 3 =
          appendGas + 53 + assignmentCost := by omega
      rw [hg]
      exact hsavePrevious
  have hsload : Func.RunCompiled fs sevm
      (base.setMach ⟨[assignmentKey], M,
        appendGas + 56 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      (Ninst.sload ::: dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ Ninst.sstore :::
        Ninst.iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    exact Func.RunCompiled.next (temporal_sload_runCompiled hassignment (by decide))
      hdup
  have htargetKeyFirst : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M,
        appendGas + 68 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      (targetKey +++ Ninst.sload ::: dup 0 :::
        mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ Ninst.sstore ::: Ninst.iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))
      post := by
    simp only [assignmentKey] at hsload
    have hrun := targetKey_prepend_runCompiled htargetValue htargetMemory
      halign htargetCovered (by simp) hsload
    have hg : appendGas + 56 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) + 12 =
        appendGas + 68 + assignmentCost +
          temporalSloadCost sevm base (assignmentSlot target) := by omega
    rw [hg] at hrun
    exact hrun
  have hguardBranch : Func.RunCompiled fs sevm
      (base.setMach ⟨[0], M,
        appendGas + 81 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ Ninst.sload ::: dup 0 :::
          mstoreAt previousPauserWord +++ loadWord newPauserWord +++
          targetKey +++ Ninst.sstore ::: Ninst.iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot))))
      post := by
    apply Func.RunCompiled.zero (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      decide)
    · have hg : appendGas + 81 + assignmentCost +
          temporalSloadCost sevm base assignmentKey =
          appendGas + 68 + assignmentCost +
            temporalSloadCost sevm base assignmentKey + 13 := by omega
      rw [hg]
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using (Devm.popBurnBy_setMach
          (devm := base.setMach ⟨[0], M,
            appendGas + 68 + assignmentCost +
              temporalSloadCost sevm base assignmentKey + 13⟩)
          (x := (0 : B256)) (s := [])
          (cost := gVerylow + gHigh)
          (G := appendGas + 68 + assignmentCost +
            temporalSloadCost sevm base assignmentKey)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh]))
    · exact htargetKeyFirst
  have hguard : Func.RunCompiled fs sevm
      (base.setMach ⟨[target], M,
        appendGas + 84 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      (Ninst.iszero ::: ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ Ninst.sload ::: dup 0 :::
          mstoreAt previousPauserWord +++ loadWord newPauserWord +++
          targetKey +++ Ninst.sstore ::: Ninst.iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ Ninst.sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ Ninst.sstore ::: .call afterOldPauserSlot)))))
      post := by
    func_run (1) [0]
    case h_val =>
      change (if target = 0 then (1 : B256) else 0) = 0
      rw [if_neg htargetValid.1]
    case a =>
      have hg : appendGas + 84 + assignmentCost +
            temporalSloadCost sevm base assignmentKey - 3 =
          appendGas + 81 + assignmentCost +
            temporalSloadCost sevm base assignmentKey := by omega
      rw [hg]
      exact hguardBranch
  have hkernel : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M,
        appendGas + 90 + assignmentCost +
          temporalSloadCost sevm base assignmentKey⟩)
      setPauserKernel post := by
    have hrun := targetWord_prepend_runCompiled htargetValue htargetMemory
      halign htargetCovered (by simp) hguard
    have hg : appendGas + 84 + assignmentCost +
          temporalSloadCost sevm base assignmentKey + 6 =
        appendGas + 90 + assignmentCost +
          temporalSloadCost sevm base assignmentKey := by omega
    rw [hg] at hrun
    simpa only [setPauserKernel] using hrun
  rcases freshRegistration_sourceTrace_witness hw htargetValid hnewValid hfind with
    ⟨trace, htrace, hpostEntries, hwrites, hwpost⟩
  refine ⟨trace, post, htrace, hpostEntries, ?_, ?_, hgas,
    hstoreExpiry, ?_⟩
  · exact hwpost
  · have hg : G + freshSetPauserKernelGas sevm base M entries target
          newPauser assignmentCost arrayCost indexCost lengthCost countCost =
        appendGas + 90 + assignmentCost +
          temporalSloadCost sevm base assignmentKey := by
      dsimp only [freshSetPauserKernelGas, appendGas, assignmentPost,
        assignmentBase, assignmentKey, next, freshAssignmentPost,
        freshAssignmentBase]
      omega
    rw [hg]
    simpa only [fs] using hkernel
  · have hbaseLogs : assignmentPost.logs = base.logs := by
      dsimp only [assignmentPost, freshAssignmentPost, freshAssignmentBase]
      rw [temporalSstorePost_logs, temporalSloadBase_logs]
    rw [hbaseLogs] at hlogs
    exact hlogs

/-! ## Fresh registration public boundary -/

private def freshRegisterMemory (target newPauser : B256) : Mem :=
  (((Mem.empty.write (targetWord * 32).toNat target.toBytes).write
      (newPauserWord * 32).toNat newPauser.toBytes).write
      (previousPauserWord * 32).toNat (0 : B256).toBytes).write
      (continuationWord * 32).toNat (0 : B256).toBytes

private def freshRegisterImage (target newPauser : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt [] (targetWord * 32).toNat target.toBytes)
        (newPauserWord * 32).toNat newPauser.toBytes)
      (previousPauserWord * 32).toNat (0 : B256).toBytes)
    (continuationWord * 32).toNat (0 : B256).toBytes

set_option maxRecDepth 4096 in
private theorem freshRegisterMemory_spec (target newPauser : B256) :
    let M := freshRegisterMemory target newPauser
    let img := freshRegisterImage target newPauser
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
  dsimp only [freshRegisterMemory, freshRegisterImage]
  exact ⟨hwf4, hreads4, hsize4, htarget4, hnew4,
    hprevious4, hcontinuation4⟩

/-- Exact gas reserve for the production `registerPauser` body on the fresh,
nonzero path, including its canonical decoder/admin prefix and real staged
memory image. -/
def freshRegisterBodyGas (sevm : Sevm) (base : Devm)
    (entries : List Entry) (target newPauser : B256)
    (assignmentCost arrayCost indexCost lengthCost countCost : Nat) : Nat :=
  221 + freshSetPauserKernelGas sevm base
    (freshRegisterMemory target newPauser) entries target newPauser
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
    (harray : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
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
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hinterval : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hexpiry : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
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
  let M := freshRegisterMemory target newPauser
  let img := freshRegisterImage target newPauser
  rcases freshRegisterMemory_spec target newPauser with
    ⟨hwf, hreads, hsize, htargetRead, hnewRead,
      hpreviousRead, hcontinuationRead⟩
  have halign : M.size % 32 = 0 := by
    change (freshRegisterMemory target newPauser).size % 32 = 0
    rw [hsize]
  rcases setPauserKernel_freshNonzero_runCompiled dp sevm base M img entries
      target newPauser timestamp interval expiry assignmentOriginal
      arrayOriginal indexOriginal lengthOriginal countOriginal assignmentCost
      arrayCost indexCost lengthCost countCost G hw hfind hwf hreads
      htargetRead hnewRead hcontinuationRead htargetValid hnewValid
      (by
        change 640 ≤ (freshRegisterMemory target newPauser).size
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
    all_goals first
      | exact Devm.extCost_of_size (n := 0) rfl (by decide +kernel)
      | exact Devm.extCost_of_size (n := 544) (hM1Size _) (by decide +kernel)
      | exact Devm.extCost_of_size (n := 576) (hM2Size _ _) (by decide +kernel)
      | exact Devm.extCost_of_size (n := 608) (hM3Size _ _) (by decide +kernel)
      | skip
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

/-- Exact generated-runtime dispatcher reserve for
`registerPauser(address,address)`. -/
def registerPauserDispatchGas : Nat := 175

set_option maxRecDepth 16384 in
private theorem registerPauser_dispatch_runCompiledTo
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
    (harray : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal sevm sevm.currentTarget
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (sevm.currentTarget,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
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
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hinterval : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = interval)
    (hintervalCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
    (hexpiry : (freshAssignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (sevm.currentTarget, expirySlot newPauser) ∈
      (freshAssignmentPost sevm base target newPauser).accessedStorageKeys)
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

private theorem registerPauserCalldata_spec (sevm : Sevm)
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
    (harray : (freshAssignmentPost (initSevm msg) (initDevm msg)
      target newPauser).getStorVal ca
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0)
    (harrayOrig : getOrigStorVal (initSevm msg) ca
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = arrayOriginal)
    (harrayCost : sstoreValueCost arrayOriginal 0 target = arrayCost)
    (hwarmArray : (ca,
      arrayEntrySlot (Nat.toB256 (entries.length + 1))) ∈
        (freshAssignmentPost (initSevm msg) (initDevm msg)
          target newPauser).accessedStorageKeys)
    (hindexOrig : getOrigStorVal (initSevm msg) ca
      (indexSlot target) = indexOriginal)
    (hindexCost : sstoreValueCost indexOriginal 0
      (Nat.toB256 (entries.length + 1)) = indexCost)
    (hwarmIndex : (ca, indexSlot target) ∈
      (freshAssignmentPost (initSevm msg) (initDevm msg)
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
      (freshAssignmentPost (initSevm msg) (initDevm msg)
        target newPauser).accessedStorageKeys)
    (hinterval : (freshAssignmentPost (initSevm msg) (initDevm msg)
      target newPauser).getStorVal ca heartbeatIntervalSlot = interval)
    (hintervalCold : (ca, heartbeatIntervalSlot) ∉
      (freshAssignmentPost (initSevm msg) (initDevm msg)
        target newPauser).accessedStorageKeys)
    (hexpiry : (freshAssignmentPost (initSevm msg) (initDevm msg)
      target newPauser).getStorVal ca (expirySlot newPauser) = 0)
    (hexpiryOrig : getOrigStorVal (initSevm msg) ca
      (expirySlot newPauser) = 0)
    (hwarmExpiry : (ca, expirySlot newPauser) ∈
      (freshAssignmentPost (initSevm msg) (initDevm msg)
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

set_option maxRecDepth 16384 in
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
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
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
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0 := by
    rw [Mem.Reads.read hreads]
    exact hprevious
  have hnewValue :
      (M.read (newPauserWord * 32).toNat 32).1.toB256 = 0 := by
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
  have hregister := registerAfterSet_absentZero_runCompiled fs sevm eventBase
    M img carry G hreads hprevious hnew hsize halign
  have hlookup : fs[registerAfterSetSlot]? = some registerAfterSet := by
    simp [fs, runtime, aux, registerAfterSetSlot]
  have hcall : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨[carry], M, G + 58⟩)
      (.call registerAfterSetSlot)
      (eventBase.setMach ⟨[carry], M, G⟩) := by
    apply Func.RunCompiled.call hlookup
      (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := eventBase.setMach ⟨[carry], M, G + 58⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G + 46)
          (by simp only [Devm.gasLeft_setMach];
              norm_num [gVerylow, gMid, gJumpdest]))
    · exact hregister
  have hbranch : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨[1, carry], M, G + 72⟩)
      ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))
      (eventBase.setMach ⟨[carry], M, G⟩) := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := eventBase.setMach ⟨[1, carry], M, G + 72⟩)
          (x := (1 : B256)) (s := [carry])
          (cost := gVerylow + gHigh + gJumpdest) (G := G + 58)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]))
    · exact hcall
  have hcontinuationRun : Func.RunCompiled fs sevm
      (eventBase.setMach ⟨[carry], M, G + 81⟩)
      (loadWord continuationWord +++ Ninst.iszero :::
        ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot)))
      (eventBase.setMach ⟨[carry], M, G⟩) := by
    func_run (3) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hcontinuationCovered]
      norm_num [gVerylow]
    case a =>
      rw [hcontinuationValue, hcontinuationMemory]
      norm_num
      exact hbranch
  simp only [finishSetPauser]
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

private def absentZeroLengthRestorePost (sevm : Sevm) (base : Devm)
    (oldLength : B256) : Devm :=
  temporalSstorePost sevm base arrayLengthSlot oldLength

private def absentZeroRemovePost (sevm : Sevm) (base : Devm)
    (target oldLength : B256) : Devm :=
  temporalSstorePost sevm
    (absentZeroLengthRestorePost sevm base oldLength)
    (indexSlot target) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem removeTarget_restoreTail_absentZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next carry : B256)
    (lengthOriginal indexOriginal : B256)
    (lengthRestoreCost indexClearCost G : Nat)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (hlengthWord : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = next)
    (htargetValid : nonzeroCanonicalAddress target)
    (hsize : 736 ≤ M.size) (halign : M.size % 32 = 0)
    (hlength : base.getStorVal sevm.currentTarget
      arrayLengthSlot = next)
    (hindex : base.getStorVal sevm.currentTarget
      (indexSlot target) = next)
    (hlengthOrig : getOrigStorVal sevm sevm.currentTarget
      arrayLengthSlot = lengthOriginal)
    (hindexOrig : getOrigStorVal sevm sevm.currentTarget
      (indexSlot target) = indexOriginal)
    (hlengthCost : sstoreValueCost lengthOriginal next oldLength =
      lengthRestoreCost)
    (hindexCost : sstoreValueCost indexOriginal next 0 = indexClearCost)
    (hwarmLength : (sevm.currentTarget, arrayLengthSlot) ∈
      base.accessedStorageKeys)
    (hwarmIndex : (sevm.currentTarget, indexSlot target) ∈
      base.accessedStorageKeys)
    (hsub : next - 1 = oldLength)
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[carry], M,
        G + 2025 + indexClearCost + lengthRestoreCost⟩)
      (loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm base target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
  dsimp only
  let indexKey := indexSlot target
  let lengthPost := absentZeroLengthRestorePost sevm base oldLength
  let removePost := absentZeroRemovePost sevm base target oldLength
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
  have hlengthFamilies := registryAddressFamilies_ne_arrayLengthSlot
    htargetValid.2 htargetValid.2
  have hindexLength : indexKey ≠ arrayLengthSlot := by
    simpa only [indexKey] using hlengthFamilies.2.1
  have hindexPost : lengthPost.getStorVal sevm.currentTarget
      indexKey = next := by
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
      (M.read (arrayLengthWord * 32).toNat 32).1.toB256 = next := by
    rw [Mem.Reads.read hreads]
    exact hlengthWord
  have hfinish := finishSetPauser_absentZero_runCompiled dp sevm removePost
    M img target carry G hreads htarget hprevious hnew hcontinuation
    (by omega) halign hstatic
  let fs := (runtime dp).main :: (runtime dp).aux
  have hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser := by
    simp [fs, runtime, aux, finishSetPauserSlot]
  have hfinishCall : Func.RunCompiled fs sevm
      (removePost.setMach ⟨[carry], M, G + 1993⟩)
      (.call finishSetPauserSlot)
      ((removePost.addLog eventLog).setMach ⟨[carry], M, G⟩) := by
    apply Func.RunCompiled.call hfinishLookup (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := removePost.setMach ⟨[carry], M, G + 1993⟩)
          (cost := gVerylow + gMid + gJumpdest) (G := G + 1981)
          (by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gMid, gJumpdest]))
    · simpa only [fs, eventLog] using hfinish
  have hstoreIndex : Func.RunCompiled fs sevm
      (lengthPost.setMach
        ⟨[indexKey, 0, carry], M, G + 1993 + indexClearCost⟩)
      (Ninst.sstore ::: .call finishSetPauserSlot)
      ((removePost.addLog eventLog).setMach ⟨[carry], M, G⟩) := by
    have hsstore : Ninst.RunCompiled sevm
        (lengthPost.setMach
          ⟨[indexKey, 0, carry], M, G + 1993 + indexClearCost⟩)
        Ninst.sstore
        (removePost.setMach ⟨[carry], M, G + 1993⟩) := by
      exact temporal_sstore_runCompiled hindexPost hindexOrig hindexCost
        hwarmIndexPost hgasFinal hstatic
    exact Func.RunCompiled.next hsstore hfinishCall
  have hindexTail : Func.RunCompiled fs sevm
      (lengthPost.setMach ⟨[carry], M, G + 2007 + indexClearCost⟩)
      (pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      ((removePost.addLog eventLog).setMach ⟨[carry], M, G⟩) := by
    have htail := hstoreIndex
    simp only [indexKey] at htail
    have hrun := pushZero_targetIndexKey_prepend_runCompiled htargetValue
      htargetMemory halign htargetCovered (by simp) htail
    have hg : G + 1993 + indexClearCost + 14 =
        G + 2007 + indexClearCost := by omega
    rw [hg] at hrun
    exact hrun
  have hstoreLength : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[arrayLengthSlot, oldLength, carry], M,
          G + 2007 + indexClearCost + lengthRestoreCost⟩)
      (Ninst.sstore ::: pushB256 0 ::: targetIndexKey +++
        Ninst.sstore ::: .call finishSetPauserSlot)
      ((removePost.addLog eventLog).setMach ⟨[carry], M, G⟩) := by
    have hsstore : Ninst.RunCompiled sevm
        (base.setMach
          ⟨[arrayLengthSlot, oldLength, carry], M,
            G + 2007 + indexClearCost + lengthRestoreCost⟩)
        Ninst.sstore
        (lengthPost.setMach
          ⟨[carry], M, G + 2007 + indexClearCost⟩) := by
      exact temporal_sstore_runCompiled hlength hlengthOrig hlengthCost
        hwarmLength (lt_of_lt_of_le hgasFinal (by omega)) hstatic
    exact Func.RunCompiled.next hsstore hindexTail
  func_run (6) [3]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hlengthCovered]
    norm_num [gVerylow]
  case a =>
    rw [hlengthValue, hlengthMemory]
    change Func.RunCompiled _ _
      (base.setMach
        ⟨[arrayLengthSlot, next - 1, carry], M,
          G + 2025 + indexClearCost + lengthRestoreCost - 18⟩)
      _ _
    rw [hsub]
    have hg : G + 2025 + indexClearCost + lengthRestoreCost - 18 =
        G + 2007 + indexClearCost + lengthRestoreCost := by omega
    rw [hg]
    exact hstoreLength

private def absentZeroHolePost (sevm : Sevm) (base : Devm)
    (target next : B256) : Devm :=
  temporalSstorePost sevm base (arrayEntrySlot next) target

private def absentZeroMovedIndexPost (sevm : Sevm) (base : Devm)
    (target next : B256) : Devm :=
  temporalSstorePost sevm (absentZeroHolePost sevm base target next)
    (indexSlot target) next

private def absentZeroTailClearPost (sevm : Sevm) (base : Devm)
    (target next : B256) : Devm :=
  temporalSstorePost sevm
    (absentZeroMovedIndexPost sevm base target next)
    (arrayEntrySlot next) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem removeTarget_storePrefix_absentZero_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target oldLength next carry : B256)
    (arrayOriginal indexOriginal lengthOriginal : B256)
    (holeCost movedIndexCost tailClearCost lengthRestoreCost
      indexClearCost G : Nat)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hprevious : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = 0)
    (hnew : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuation : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
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
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[carry], M,
        G + 2075 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost⟩)
      (loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++
        Ninst.sstore ::: pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], M, G⟩) := by
  dsimp only
  let arrayKey := arrayEntrySlot next
  let indexKey := indexSlot target
  let holePost := absentZeroHolePost sevm base target next
  let movedPost := absentZeroMovedIndexPost sevm base target next
  let tailPost := absentZeroTailClearPost sevm base target next
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
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
    simpa only [holePost, absentZeroHolePost, arrayKey] using
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
    simpa only [movedPost, absentZeroMovedIndexPost, indexKey,
      holePost, absentZeroHolePost] using
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
  have hrestore := removeTarget_restoreTail_absentZero_runCompiled
    dp sevm tailPost M img target oldLength next carry lengthOriginal
    indexOriginal lengthRestoreCost indexClearCost G hreads htarget
    hprevious hnew hcontinuation hlengthWord htargetValid hsize halign
    hlengthTail hindexTail hlengthOrig hindexOrig hlengthRestoreCost
    hindexClearCost hwarmLengthTail hwarmIndexTail hsub hgasFinal hstatic
  let fs := (runtime dp).main :: (runtime dp).aux
  have hrestore' : Func.RunCompiled fs sevm
      (tailPost.setMach
        ⟨[carry], M,
          G + 2025 + lengthRestoreCost + indexClearCost⟩)
      (loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    have hg : G + 2025 + lengthRestoreCost + indexClearCost =
        G + 2025 + indexClearCost + lengthRestoreCost := by omega
    rw [hg]
    simpa only [fs, eventLog] using hrestore
  have hstoreTail : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨[arrayKey, 0, carry], M,
          G + 2025 + lengthRestoreCost + indexClearCost + tailClearCost⟩)
      (Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled harrayMoved harrayOrig htailClearCost
        hwarmArrayMoved (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      hrestore'
  have htailTag : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨[next, 0, carry], M,
          G + 2031 + lengthRestoreCost + indexClearCost + tailClearCost⟩)
      (tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [arrayKey]
    case a =>
      have hg : G + 2031 + lengthRestoreCost + indexClearCost +
          tailClearCost - 6 =
          G + 2025 + lengthRestoreCost + indexClearCost +
            tailClearCost := by omega
      rw [hg]
      exact hstoreTail
  have htailLength : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨[0, carry], M,
          G + 2037 + lengthRestoreCost + indexClearCost + tailClearCost⟩)
      (loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered arrayLengthWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlengthValue, hlengthMemory]
      have hg : G + 2037 + lengthRestoreCost + indexClearCost +
          tailClearCost - 6 =
          G + 2031 + lengthRestoreCost + indexClearCost +
            tailClearCost := by omega
      rw [hg]
      exact htailTag
  have htailPrefix : Func.RunCompiled fs sevm
      (movedPost.setMach
        ⟨[carry], M,
          G + 2039 + lengthRestoreCost + indexClearCost + tailClearCost⟩)
      (pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (1)
    case a =>
      have hg : G + 2039 + lengthRestoreCost + indexClearCost +
          tailClearCost - 2 =
          G + 2037 + lengthRestoreCost + indexClearCost +
            tailClearCost := by omega
      rw [hg]
      exact htailLength
  have hstoreMoved : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨[indexKey, next, carry], M,
          G + 2039 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (Ninst.sstore ::: pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord arrayLengthWord +++
        pushB256 1 ::: swap 0 ::: sub ::: pushB256 arrayLengthSlot :::
        Ninst.sstore ::: pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled hindexHole hindexOrig hmovedIndexCost
        hwarmIndexHole (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      htailPrefix
  have hmovedTag : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨[target, next, carry], M,
          G + 2045 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [indexKey]
    case a =>
      have hg : G + 2045 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost - 6 =
          G + 2039 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost := by omega
      rw [hg]
      exact hstoreMoved
  have hmovedLast : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨[next, carry], M,
          G + 2051 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered lastTargetWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlastValue, hlastMemory]
      have hg : G + 2051 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost - 6 =
          G + 2045 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost := by omega
      rw [hg]
      exact hmovedTag
  have hmovedPrefix : Func.RunCompiled fs sevm
      (holePost.setMach
        ⟨[carry], M,
          G + 2057 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost⟩)
      (loadWord removedIndexWord +++ loadWord lastTargetWord +++
        tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered removedIndexWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hremovedValue, hremovedMemory]
      have hg : G + 2057 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost - 6 =
          G + 2051 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost := by omega
      rw [hg]
      exact hmovedLast
  have hstoreHole : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[arrayKey, target, carry], M,
          G + 2057 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (Ninst.sstore ::: loadWord removedIndexWord +++
        loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    exact Func.RunCompiled.next
      (temporal_sstore_runCompiled harray harrayOrig hholeCost hwarmArray
        (lt_of_lt_of_le hgasFinal (by omega)) hstatic)
      hmovedPrefix
  have hholeTag : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[next, target, carry], M,
          G + 2063 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        loadWord lastTargetWord +++ tagTop indexRegion +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [arrayKey]
    case a =>
      have hg : G + 2063 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost + holeCost - 6 =
          G + 2057 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost := by omega
      rw [hg]
      exact hstoreHole
  have hholeRemoved : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[target, carry], M,
          G + 2069 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ loadWord lastTargetWord +++
        tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered removedIndexWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hremovedValue, hremovedMemory]
      have hg : G + 2069 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost + holeCost - 6 =
          G + 2063 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost := by omega
      rw [hg]
      exact hholeTag
  have hholePrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[carry], M,
          G + 2075 + lengthRestoreCost + indexClearCost + tailClearCost +
            movedIndexCost + holeCost⟩)
      (loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ loadWord lastTargetWord +++
        tagTop indexRegion +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm tailPost target oldLength).addLog
        eventLog).setMach ⟨[carry], M, G⟩) := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (covered lastTargetWord (by decide))]
      norm_num [gVerylow]
    case a =>
      rw [hlastValue, hlastMemory]
      have hg : G + 2075 + lengthRestoreCost + indexClearCost +
          tailClearCost + movedIndexCost + holeCost - 6 =
          G + 2069 + lengthRestoreCost + indexClearCost +
            tailClearCost + movedIndexCost + holeCost := by omega
      rw [hg]
      exact hholeRemoved
  have hg : G + 2075 + lengthRestoreCost + indexClearCost + tailClearCost +
      movedIndexCost + holeCost =
      G + 2075 + holeCost + movedIndexCost + tailClearCost +
        lengthRestoreCost + indexClearCost := by omega
  rw [hg] at hholePrefix
  simpa only [lastTargetIndexKey, prepend_append, fs, eventLog,
    arrayKey, indexKey, holePost, movedPost, tailPost] using hholePrefix

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem removeTarget_absentZero_runCompiled
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
    (hgasFinal : gCallStipend < G + 1993 + indexClearCost)
    (hstatic : sevm.isStatic = false) :
    let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
    let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
    let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
    let eventLog : Log :=
      ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
    Func.RunCompiled ((runtime dp).main :: (runtime dp).aux) sevm
      (base.setMach ⟨[carry], M,
        G + 2424 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost⟩)
      removeTarget
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
  dsimp only
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
  have hpreviousLast : Bytes.toB256
      (imgLast.sliceD (previousPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hprevious
  have hnewLast : Bytes.toB256
      (imgLast.sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hnew
  have hcontinuationLast : Bytes.toB256
      (imgLast.sliceD (continuationWord * 32).toNat 32 0) = 0 :=
    (earlierLast (by decide) (by decide) (by decide)).trans hcontinuation
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
  have hstores := removeTarget_storePrefix_absentZero_runCompiled
    dp sevm base MLast imgLast target oldLength next carry arrayOriginal
    indexOriginal lengthOriginal holeCost movedIndexCost tailClearCost
    lengthRestoreCost indexClearCost G hreadsLast htargetLast hpreviousLast
    hnewLast hcontinuationLast hremovedLast hlengthLast hlastLast
    htargetValid hnextNonzero hnextBound (by rw [hsizeLast]) halignLast
    harray hindex
    hlength harrayOrig hindexOrig hlengthOrig hholeCost hmovedIndexCost
    htailClearCost hlengthRestoreCost hindexClearCost hwarmArray hwarmIndex
    hwarmLength hsub hgasFinal hstatic
  let fs := (runtime dp).main :: (runtime dp).aux
  have hsaveLast : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[lastTargetWord * 32, target, carry], MLength,
          G + 2082 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
      (Ninst.mstore ::: loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_mstore_of
        (G := G + 2075 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) (M := MLast) rfl
        (Devm.extCost_of_size
          (i := (lastTargetWord * 32).toNat) (sz := 32) (e := 4)
          hsizeLength (by decide))
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · simpa only [fs, eventLog, MLast, Devm.setMach_setMach,
        Devm.memory_setMach] using hstores
  have hlastLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[target, carry], MLength,
          G + 2085 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
      (mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    func_run (1)
    case a =>
      have hg : G + 2085 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 3 =
          G + 2082 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hsaveLast
  have hloadLastStorage : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[arrayKey, carry], MLength,
          G + 2185 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
      (Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmArray
        (by simpa only [Devm.getStorVal_setMach, arrayKey] using harray)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by simp))
      hlastLoad
  have hlastTag : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[next, carry], MLength,
          G + 2191 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
      (tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    func_run (2) [arrayKey]
    case a =>
      have hg : G + 2191 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 6 =
          G + 2185 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost := by omega
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
      rw [hsizeLength]
      decide))]
  have hlastPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[carry], MLength,
          G + 2197 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
      (loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sload :::
        mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ Ninst.sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sstore ::: loadWord arrayLengthWord +++ pushB256 1 :::
        swap 0 ::: sub ::: pushB256 arrayLengthSlot ::: Ninst.sstore :::
        pushB256 0 ::: targetIndexKey +++ Ninst.sstore :::
        .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    func_run (2) [3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halignLength (by
        rw [hsizeLength]
        decide)]
      norm_num [gVerylow]
    case a =>
      rw [hlengthValue, hlengthMemory]
      have hg : G + 2197 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 6 =
          G + 2191 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hlastTag
  have hsaveLength : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[arrayLengthWord * 32, next, carry], MIndex,
          G + 2200 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
      (Ninst.mstore ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_mstore_of
        (G := G + 2197 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) (M := MLength) rfl
        (Devm.extCost_of_size
          (i := (arrayLengthWord * 32).toNat) (sz := 32) (e := 0)
          hsizeIndex (by decide))
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlastPrefix
  have hsaveLengthPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[next, carry], MIndex,
          G + 2203 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
      (mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
        tagTop arrayRegion +++ Ninst.sload ::: mstoreAt lastTargetWord +++
        loadWord lastTargetWord +++ loadWord removedIndexWord +++
        tagTop arrayRegion +++ Ninst.sstore ::: loadWord removedIndexWord +++
        lastTargetIndexKey +++ Ninst.sstore ::: pushB256 0 :::
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ Ninst.sstore :::
        loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
        pushB256 arrayLengthSlot ::: Ninst.sstore ::: pushB256 0 :::
        targetIndexKey +++ Ninst.sstore ::: .call finishSetPauserSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    func_run (1)
    case a =>
      have hg : G + 2203 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 3 =
          G + 2200 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hsaveLength
  have hlengthLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[arrayLengthSlot, carry], MIndex,
          G + 2303 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmLength
        (by simpa only [Devm.getStorVal_setMach] using hlength)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by simp))
      hsaveLengthPrefix
  have hlengthPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[carry], MIndex,
          G + 2306 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    func_run (1)
    case a =>
      have hg : G + 2306 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 3 =
          G + 2303 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hlengthLoad
  have hsaveIndex : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[removedIndexWord * 32, next, carry], M,
          G + 2309 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_mstore_of
        (G := G + 2306 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost) (M := MIndex) rfl
        (Devm.extCost_of_size
          (i := (removedIndexWord * 32).toNat) (sz := 32) (e := 0)
          hsize (by decide))
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl
    · exact hlengthPrefix
  have hsaveIndexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[next, carry], M,
          G + 2312 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    func_run (1)
    case a =>
      have hg : G + 2312 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 3 =
          G + 2309 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hsaveIndex
  have hindexLoad : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[indexKey, carry], M,
          G + 2412 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost⟩)
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    exact Func.RunCompiled.next
      (Ninst.runCompiled_sload_warm rfl hwarmIndex
        (by simpa only [Devm.getStorVal_setMach, indexKey] using hindex)
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)
        (by simp))
      hsaveIndexPrefix
  have htargetValue :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  have htargetMemory :
      (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign (by
      rw [hsize]
      decide))]
  have hindexPrefix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[carry], M,
          G + 2424 + holeCost + movedIndexCost + tailClearCost +
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    func_run (4) [3, indexKey]
    all_goals try {
      simpa [indexKey, indexSlot, slot] using
        congrArg (fun x : B256 => (regionWord indexRegion).or x)
          htargetValue }
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign (by
        rw [hsize]
        decide)]
      norm_num [gVerylow]
    case a =>
      rw [htargetMemory]
      have hg : G + 2424 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 12 =
          G + 2412 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost := by omega
      rw [hg]
      exact hindexLoad
  simp only [removeTarget]
  simpa only [fs, eventLog, MLast] using hindexPrefix

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
  dsimp only
  let fs := (runtime dp).main :: (runtime dp).aux
  let MIndex := M.write (removedIndexWord * 32).toNat next.toBytes
  let MLength := MIndex.write (arrayLengthWord * 32).toNat next.toBytes
  let MLast := MLength.write (lastTargetWord * 32).toNat target.toBytes
  let eventLog : Log :=
    ⟨sevm.currentTarget, [pauserSetEvent, target, 0, 0], []⟩
  have hremove := removeTarget_absentZero_runCompiled dp sevm base M img
    target oldLength next carry arrayOriginal indexOriginal lengthOriginal
    holeCost movedIndexCost tailClearCost lengthRestoreCost indexClearCost G
    hwf hreads htarget hprevious hnew hcontinuation htargetValid
    hnextNonzero hnextBound hsize halign harray hindex hlength harrayOrig
    hindexOrig hlengthOrig hholeCost hmovedIndexCost htailClearCost
    hlengthRestoreCost hindexClearCost hwarmArray hwarmIndex hwarmLength
    hsub hgasFinal hstatic
  have hlookup : fs[removeTargetSlot]? = some removeTarget := by
    simp [fs, runtime, aux, removeTargetSlot]
  have hcall : Func.RunCompiled fs sevm
      (base.setMach ⟨[carry], M,
        G + 2436 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost⟩)
      (.call removeTargetSlot)
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    apply Func.RunCompiled.call hlookup (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.burnBy_setMach_gas
          (devm := base.setMach ⟨[carry], M,
            G + 2436 + holeCost + movedIndexCost + tailClearCost +
              lengthRestoreCost + indexClearCost⟩)
          (cost := gVerylow + gMid + gJumpdest)
          (G := G + 2424 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost)
          (by simp only [Devm.gasLeft_setMach]
              norm_num [gVerylow, gMid, gJumpdest]
              omega))
    · simpa only [fs, MIndex, MLength, MLast, eventLog] using hremove
  have hbranch : Func.RunCompiled fs sevm
      (base.setMach ⟨[1, carry], M,
        G + 2450 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost⟩)
      ((.call removeTargetSlot) <?>
        (newCountKey +++ Ninst.sload ::: pushB256 1 ::: add :::
          newCountKey +++ Ninst.sstore ::: .call finishSetPauserSlot))
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm base target next)
          target oldLength).addLog eventLog).setMach
        ⟨[carry], MLast, G⟩) := by
    apply Func.RunCompiled.succ (w := (1 : B256)) (by decide) (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      decide)
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
        (Devm.popBurnBy_setMach
          (devm := base.setMach ⟨[1, carry], M,
            G + 2450 + holeCost + movedIndexCost + tailClearCost +
              lengthRestoreCost + indexClearCost⟩)
          (x := (1 : B256)) (s := [carry])
          (cost := gVerylow + gHigh + gJumpdest)
          (G := G + 2436 + holeCost + movedIndexCost + tailClearCost +
            lengthRestoreCost + indexClearCost)
          (h_stk := rfl) (h := by
            simp only [Devm.gasLeft_setMach]
            norm_num [gVerylow, gHigh, gJumpdest]
            omega))
    · exact hcall
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    rw [hsize]
    decide
  have hnewMemory : (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  simp only [afterOldPauser]
  func_run (3) [3]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hnewCovered]
    norm_num [gVerylow]
  case a =>
    rw [Mem.Reads.read hreads, hnew, hnewMemory]
    have hg : G + 2459 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost - 9 =
        G + 2450 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost := by omega
    rw [hg]
    exact hbranch

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
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
        afterGas + 75 + freshArrayLengthMemoryCost M +
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
  have hmemoryCost : freshArrayLengthMemoryCost M = 6 := by
    simp only [freshArrayLengthMemoryCost, hsize]
    decide +kernel
  have harithmetic : Func.RunCompiled fs sevm
      (lengthBase.setMach ⟨[length], M,
        afterGas + 72 + freshArrayLengthMemoryCost M +
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
        afterGas + 72 + freshArrayLengthMemoryCost M +
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
    have hg : afterGas + 75 + freshArrayLengthMemoryCost M +
          temporalSloadCost sevm base arrayLengthSlot +
          arrayCost + indexCost + lengthCost - 3 =
        afterGas + 72 + freshArrayLengthMemoryCost M +
          arrayCost + indexCost + lengthCost +
          temporalSloadCost sevm base arrayLengthSlot := by omega
    rw [hg]
    exact hload

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
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
      (((absentZeroRemovePost sevm
          (absentZeroTailClearPost sevm lengthPost target next)
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
    (((absentZeroRemovePost sevm
        (absentZeroTailClearPost sevm lengthPost target next)
        target oldLength).addLog eventLog).setMach
      ⟨[next], MLast, G⟩)
    hwf hreads htarget hsize htargetValid hnextNonzero hnextBound hlength
    hlengthNext harray harrayOrig harrayCost hwarmArray hindex hindexOrig
    hindexCost hwarmIndex hlengthOrig hlengthCost (by omega) hstatic hafter
  have hmemoryCost : freshArrayLengthMemoryCost M = 6 := by
    simp only [freshArrayLengthMemoryCost, hsize]
    decide +kernel
  have hg : G + 2540 + temporalSloadCost sevm base arrayLengthSlot +
        arrayCost + indexCost + lengthCost + holeCost + movedIndexCost +
        tailClearCost + lengthRestoreCost + indexClearCost =
      G + 2459 + holeCost + movedIndexCost + tailClearCost +
          lengthRestoreCost + indexClearCost + 75 +
        freshArrayLengthMemoryCost M +
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
    (absentZeroRemovePost sevm
        (absentZeroTailClearPost sevm lengthPost target next)
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
  simp only [absentZeroRemovePost, absentZeroLengthRestorePost,
    absentZeroTailClearPost, absentZeroMovedIndexPost, absentZeroHolePost]
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
    ((absentZeroRemovePost sevm
        (absentZeroTailClearPost sevm lengthPost target next)
        target oldLength).addLog eventLog).logs =
      base.logs ++ [eventLog] := by
  dsimp only
  simp only [absentZeroRemovePost, absentZeroLengthRestorePost,
    absentZeroTailClearPost, absentZeroMovedIndexPost, absentZeroHolePost]
  have logs_addLog (d : Devm) (log : Log) :
      (d.addLog log).logs = d.logs ++ [log] := rfl
  rw [logs_addLog]
  congr 1
  rw [temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSstorePost_logs, temporalSstorePost_logs,
    temporalSloadBase_logs]

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
    let finalStorage := absentZeroRemovePost sevm
      (absentZeroTailClearPost sevm lengthPost target next)
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
  · simp only [absentZeroRemovePost, absentZeroLengthRestorePost,
      absentZeroTailClearPost, absentZeroMovedIndexPost, absentZeroHolePost]
    rw [temporalSstorePost_other _ _ indexKey 0 _ arrayKey
        (pairNe (Ne.symm harrayFamilies.2.1)),
      temporalSstorePost_other _ _ arrayLengthSlot oldLength _ arrayKey
        (pairNe (Ne.symm hlengthArray)),
      temporalSstorePost_self]
    exact harray.symm
  constructor
  · simp only [absentZeroRemovePost]
    rw [temporalSstorePost_self]
    exact hindex.symm
  · simp only [absentZeroRemovePost, absentZeroLengthRestorePost]
    rw [temporalSstorePost_other _ _ indexKey 0 _ arrayLengthSlot
        (pairNe (Ne.symm hlengthFamilies.2.1)),
      temporalSstorePost_self]
    exact hlength.symm

end Blanc.LidoCircuitBreaker
