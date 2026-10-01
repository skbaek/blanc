import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteRegistry
import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserNonzero

/-!
# Finite deployed-registry update

`registryModelStorage` is a synthetic logical object constructed from finite
entry data. Its global logical witness is a proof device; it is never an
assumed witness of actual EVM storage and uses no hashing premise.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc.LidoCircuitBreaker

/-- Logical completion of finite entry data, with no raw storage or hashing. -/
def registryModelStorage (entries : List LidoCircuitBreaker.Entry) : LogicalStorage :=
  { read := fun key =>
      let region := key.toNat / 2 ^ 252
      let payload := Nat.toB256 (key.toNat % 2 ^ 252)
      if region = assignmentRegion then assignmentAt entries payload
      else if region = indexRegion then Nat.toB256 (oneBasedIndexAt entries payload)
      else if region = countRegion then Nat.toB256 (assignmentCount entries payload)
      else if region = arrayRegion then
        if payload = 0 then Nat.toB256 entries.length
        else targetAt entries (payload.toNat - 1)
      else 0 }

theorem registryModelStorage_assignment (entries : List LidoCircuitBreaker.Entry) {p : B256}
    (hp : canonicalAddress p) :
    (registryModelStorage entries).read (assignmentSlot p) = assignmentAt entries p := by
  have h := tagged_region_payload (region := assignmentRegion)
    (by norm_num [assignmentRegion]) (canonicalAddress_payload_lt hp)
  simp only [assignmentSlot, registryModelStorage, h.1, h.2]
  simp only [↓reduceIte]

theorem registryModelStorage_index (entries : List LidoCircuitBreaker.Entry) {p : B256}
    (hp : canonicalAddress p) :
    (registryModelStorage entries).read (indexSlot p) = Nat.toB256 (oneBasedIndexAt entries p) := by
  have h := tagged_region_payload (region := indexRegion)
    (by norm_num [indexRegion]) (canonicalAddress_payload_lt hp)
  simp only [indexSlot, registryModelStorage, h.1, h.2]
  simp only [indexRegion, assignmentRegion, Nat.succ_ne_self, ↓reduceIte]

theorem registryModelStorage_count (entries : List LidoCircuitBreaker.Entry) {p : B256}
    (hp : canonicalAddress p) :
    (registryModelStorage entries).read (countSlot p) = Nat.toB256 (assignmentCount entries p) := by
  have h := tagged_region_payload (region := countRegion)
    (by norm_num [countRegion]) (canonicalAddress_payload_lt hp)
  simp only [countSlot, registryModelStorage, h.1, h.2]
  simp only [countRegion, assignmentRegion, Nat.reduceEqDiff, ↓reduceIte, indexRegion,
    Nat.succ_ne_self]

theorem registryModelStorage_length (entries : List LidoCircuitBreaker.Entry) :
    (registryModelStorage entries).read arrayLengthSlot = Nat.toB256 entries.length := by
  have h := tagged_region_payload (region := arrayRegion) (payload := 0)
    (by norm_num [arrayRegion]) (by change (0 : Nat) < 2 ^ 252; norm_num)
  simp only [arrayLengthSlot, registryModelStorage, h.1, h.2]
  simp only [arrayRegion, assignmentRegion, Nat.reduceEqDiff, ↓reduceIte, indexRegion, countRegion,
    Nat.succ_ne_self]

theorem registryModelStorage_array (entries : List LidoCircuitBreaker.Entry) {i : Nat}
    (hi : i + 1 < 2 ^ 252) :
    (registryModelStorage entries).read (arrayEntrySlot (Nat.toB256 (i + 1))) =
      targetAt entries i := by
  have h256 : i + 1 < 2 ^ 256 := by omega
  have hword : (Nat.toB256 (i + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt h256]; exact hi
  have h := tagged_region_payload (region := arrayRegion)
    (by norm_num [arrayRegion]) hword
  have hnz : Nat.toB256 (i + 1) ≠ 0 := by
    intro heq
    have hn := congrArg B256.toNat heq
    rw [B256.toNat_toB256_of_lt h256] at hn
    simp only [B256.toNat_zero] at hn
    omega
  simp only [arrayEntrySlot, registryModelStorage, h.1, h.2]
  simp only [arrayRegion, assignmentRegion, Nat.reduceEqDiff, ↓reduceIte, indexRegion, countRegion,
    Nat.succ_ne_self, hnz, B256.toNat_toB256_of_lt h256, add_tsub_cancel_right]

/-- Finite validity suffices to construct a full witness of the synthetic model. -/
theorem registryModelWitness {entries : List LidoCircuitBreaker.Entry}
    (hlen : entries.length < 2 ^ 252) (hn : (entries.map Prod.fst).Nodup)
    (ht : ∀ e ∈ entries, nonzeroCanonicalAddress e.1)
    (hp : ∀ e ∈ entries, nonzeroCanonicalAddress e.2) :
    RegistryWitness (registryModelStorage entries) entries := by
  refine ⟨hn, ht, hp, registryModelStorage_length entries, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact registryModelStorage_array entries (by omega)
  · intro p hp; exact registryModelStorage_assignment entries hp
  · intro p hp; exact registryModelStorage_index entries hp
  · intro p hp; exact registryModelStorage_count entries hp
  · rw [registryModelStorage_count entries (by change (0 : Nat) < 2 ^ 160; norm_num)]
    have hc : assignmentCount entries 0 = 0 := by
      clear hlen hn ht
      induction entries with
      | nil => rfl
      | cons e rest ih =>
        have hne := (hp e (by simp only [List.mem_cons, true_or])).1
        have hr : ∀ e ∈ rest, nonzeroCanonicalAddress e.2 :=
          fun e he => hp e (List.mem_cons_of_mem _ he)
        simp only [assignmentCount, ite_eq_right hne, Nat.zero_add]
        exact ih hr
    rw [hc]; rfl

/-- Restrict a logical model witness to an explicit finite probe list. -/
theorem registryOn_of_modelWitness {storage : LogicalStorage} {entries : List LidoCircuitBreaker.Entry} {probes : List B256}
    (h : RegistryWitness storage entries) (hp : ∀ p ∈ probes, canonicalAddress p) :
    RegistryOn storage entries probes := by
  exact ⟨h.entries_length_lt_2pow252, h.targetsNodup, h.targetsValid, h.pausersValid,
    hp, h.lengthWord, fun i hi => h.arrayWords i (List.mem_range.mp hi),
    fun p hpm => h.assignments p (hp p hpm), fun p hpm => h.indices p (hp p hpm),
    fun p hpm => h.counts p (hp p hpm)⟩

/-- Actual finite observations agree with the synthetic model exactly where queried. -/
theorem RegistryOn.eq_model_reads {storage : LogicalStorage} {entries : List LidoCircuitBreaker.Entry}
    {probes : List B256} (h : RegistryOn storage entries probes) {key : B256}
    (hk : key ∈ registryQueries probes entries.length) :
    storage.read key = (registryModelStorage entries).read key := by
  simp only [registryQueries, List.mem_cons, List.mem_append, or_assoc] at hk
  rcases hk with rfl | ha | hm
  · rw [h.lengthWord, registryModelStorage_length]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [h.arrayWords i hi, registryModelStorage_array entries (by
      have := List.mem_range.mp hi; have := h.lengthLt; omega)]
  · obtain ⟨p, hp, hk⟩ := List.mem_flatMap.mp hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · rw [h.assignments p hp, registryModelStorage_assignment entries (h.probesValid p hp)]
    · rw [h.indices p hp, registryModelStorage_index entries (h.probesValid p hp)]
    · rw [h.counts p hp, registryModelStorage_count entries (h.probesValid p hp)]

/-- Finite raw-write transport of the existing-target update. The full logical
witness used here belongs only to the synthetic pure model. -/
theorem RegistryOn.rawNonzero {before after : Stor} {entries : List LidoCircuitBreaker.Entry}
    {probes : List B256} {target newPauser oldPauser : B256} {index : Nat}
    (hw : RegistryOn (solRegistryStorage before) entries probes)
    (htarget : nonzeroCanonicalAddress target) (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : Blanc.SlotFootprint.checkFaithfulOn solKey
      (registryQueries probes entries.length)
      ((nonzeroWrites entries target newPauser oldPauser).map Prod.fst) = true)
    (hwrites : ∀ key, after.get key =
      (rawNonzeroPost before entries target newPauser oldPauser).get key) :
    RegistryOn (solRegistryStorage after) (setEntryAt index (target, newPauser) entries) probes := by
  have hold := hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hmodel := registryModelWitness hw.lengthLt hw.targetsNodup hw.targetsValid hw.pausersValid
  have hlogical : RegistryWitness
      { read := fun key => (nonzeroWrites entries target newPauser oldPauser).foldl
          (fun cur w => if w.1 = key then w.2 else cur) ((registryModelStorage entries).read key) }
      (setEntryAt index (target, newPauser) entries) := by
    apply RegistryWitness.applyFoundNonzeroWritesOfReadEffect hmodel htarget hnew hfind
    intro key; rfl
  apply (registryOn_of_modelWitness hlogical hw.probesValid).of_read_eq
  intro key hk
  rw [setEntryAt_length_of_findEntry hfind] at hk
  have hobs := registryQueries_observable hw.probesValid hk
  have hwell := nonzeroWrites_wellFormed hw.lengthLt htarget hnew hold
  have hcongr := solRegistryStorage_read_congr hw.lengthLt hobs (hwrites (solKey key))
  rw [hcongr]
  unfold rawNonzeroPost
  rw [solRegistryStorage_applyRegistryRawWrites_at hw.lengthLt
    (fun t ht => (Blanc.SlotFootprint.checkFaithfulOn_eq_true.mp hfaithful) t ht key hk)
    hwell.1 hwell.2 hobs]
  exact congrArg (fun value => (nonzeroWrites entries target newPauser oldPauser).foldl
    (fun cur w => if w.1 = key then w.2 else cur) value) (hw.eq_model_reads hk)

/-- The updater's three raw-slot comparisons are consequences of the finite
checked write/query rows. The old/new count keys may coincide only when their
logical pauser words coincide. -/
theorem nonzeroSlotsApart_of_check {entries : List LidoCircuitBreaker.Entry}
    {probes : List B256} {target newPauser oldPauser : B256}
    (hp : ∀ p ∈ probes, canonicalAddress p)
    (ht : target ∈ probes) (ho : oldPauser ∈ probes) (hn : newPauser ∈ probes)
    (hcheck : Blanc.SlotFootprint.checkFaithfulOn solKey (registryQueries probes entries.length)
      ((nonzeroWrites entries target newPauser oldPauser).map Prod.fst) = true) :
    mapSlot target 3 ≠ mapSlot oldPauser 6 ∧
    mapSlot target 3 ≠ mapSlot newPauser 6 ∧
    (oldPauser ≠ newPauser → mapSlot oldPauser 6 ≠ mapSlot newPauser 6) := by
  have hf := Blanc.SlotFootprint.checkFaithfulOn_eq_true.mp hcheck
  have htq : assignmentSlot target ∈ registryQueries probes entries.length :=
    mem_registryQueries_mapping ht (by simp only [List.mem_cons, List.not_mem_nil, or_false,
      true_or])
  have hoq : countSlot oldPauser ∈ registryQueries probes entries.length :=
    mem_registryQueries_mapping ho (by simp only [List.mem_cons, List.not_mem_nil, or_false,
      or_true])
  have hwo : countSlot oldPauser ∈ (nonzeroWrites entries target newPauser oldPauser).map Prod.fst := by
    simp only [nonzeroWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, true_or, or_true]
  have hwn : countSlot newPauser ∈ (nonzeroWrites entries target newPauser oldPauser).map Prod.fst := by
    simp only [nonzeroWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [← solKey_assignmentSlot (hp target ht), ← solKey_countSlot (hp oldPauser ho)]
    intro heq
    exact (registryAddressFamilies_pairwise (hp target ht) (hp target ht) (hp oldPauser ho)).2.1
      (hf _ hwo _ htq heq)
  · rw [← solKey_assignmentSlot (hp target ht), ← solKey_countSlot (hp newPauser hn)]
    intro heq
    exact (registryAddressFamilies_pairwise (hp target ht) (hp target ht) (hp newPauser hn)).2.1
      (hf _ hwn _ htq heq)
  · intro hne
    rw [← solKey_countSlot (hp oldPauser ho), ← solKey_countSlot (hp newPauser hn)]
    intro heq
    exact hne (countSlot_injective (hp oldPauser ho) (hp newPauser hn) (hf _ hwn _ hoq heq))

/-- The actual entry-32 update establishes finite post-state agreement and
returns to its exact caller stack. All state and separation reads are finite. -/
theorem setPauser_nonzero_finite {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {target newPauser oldPauser ra : B256} {base : List B256} {post : Devm}
    {entries : List LidoCircuitBreaker.Entry} {probes : List B256} {index : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M ∧ M.size % 32 = 0)
    (hw : RegistryOn (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries probes)
    (ht : target ∈ probes) (ho : oldPauser ∈ probes) (hn : newPauser ∈ probes)
    (hnew : newPauser ≠ 0) (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : Blanc.SlotFootprint.checkFaithfulOn solKey (registryQueries probes entries.length)
      ((nonzeroWrites entries target newPauser oldPauser).map Prod.fst) = true)
    (run : SFunc.Run prog sevm (St b (newPauser :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    RegistryOn (solRegistryStorage (Devm.getStor post sevm.currentTarget))
      (setEntryAt index (target, newPauser) entries) probes ∧
    ∃ b2 M2 G2, post = St b2 base M2 G2 := by
  have htarget := hw.targetsValid (target, oldPauser) (mem_of_findEntry hfind)
  have hold := hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hnewc : nonzeroCanonicalAddress newPauser := ⟨hnew, hw.probesValid newPauser hn⟩
  have hassign : addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) = oldPauser := by
    have h := hw.assignments target ht
    rw [solRegistryStorage_assignment _ _ htarget.2, findEntry_assignmentAt hfind] at h
    exact h
  have hcountOld : b.getStorVal sevm.currentTarget (mapSlot oldPauser 6) =
      Nat.toB256 (assignmentCount entries oldPauser) := by
    have h := hw.counts oldPauser ho
    rw [solRegistryStorage_count _ _ hold.2] at h
    exact h
  have hcountNew : b.getStorVal sevm.currentTarget (mapSlot newPauser 6) =
      Nat.toB256 (assignmentCount entries newPauser) := by
    have h := hw.counts newPauser hn
    rw [solRegistryStorage_count _ _ hnewc.2] at h
    exact h
  obtain ⟨hsep1, hsep2, hsep3⟩ := nonzeroSlotsApart_of_check hw.probesValid ht ho hn hfaithful
  obtain ⟨hwrites, -, b2, data, M2, G2, hpost, -⟩ :=
    setPauser_nonzero_inv_of_reads hfork hmem.1 hmem.2 htarget hnewc hfind hold hw.lengthLt
      hassign hcountOld hcountNew hsep1 hsep2 hsep3 run
  exact ⟨hw.rawNonzero htarget hnewc hfind hfaithful hwrites,
    b2.addLog ⟨sevm.currentTarget, [pauserSetTopic, target, oldPauser, newPauser], data⟩,
    M2, G2, hpost⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
