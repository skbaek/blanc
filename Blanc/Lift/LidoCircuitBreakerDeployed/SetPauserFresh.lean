import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserRemoval

/-! Inversion of `Registry.setPauser`'s absent-target push block
`t_0a16_c32` on the exact deployed CircuitBreaker bytecode, and the two
absent-target branches built on it: fresh (nonzero new pauser) and
absent-zero (zero new pauser: push, then the removal arm's swap-and-pop). -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.LidoCircuitBreaker

section Blocks

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}

/-- The contract storage the push block `t_0a16_c32` leaves, as a function of
the storage `s` it starts from: the length is bumped first, then the new
element (keeping the slot's upper 96 bits) and the target's one-based index
(re-read from the length slot) are written. -/
def pushStor (s : Stor) (target : B256) : Stor :=
  let s1 := s.set 5 (s.get 5 + 1)
  let e := s.get 5 + registryArrayBase
  let s2 := s1.set e (target ||| (addressMask &&& s1.get e))
  s2.set (mapSlot target 4) (s2.get 5)

/-- `t_0a16_c32`: push the target onto the array and record its index, then
fall through to entry 4. -/
theorem t0a16_inv {newP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (htarget : canonicalAddress target)
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (0 :: newP :: target :: 3 :: R :: base) M G)
      t_0a16_c32 (.done (.returned post))) :
    ∃ b' G', StorStep sevm b b' (pushStor (Devm.getStor b sevm.currentTarget) target) ∧
      SFunc.RunCut prog sevm []
        (St b' (0 :: newP :: target :: 3 :: R :: base)
          (((M.write 0 (5 : B256).toBytes).write 0 target.toBytes).write 32 (4 : B256).toBytes) G')
        t_0a81_c4 (.done (.returned post)) := by
  obtain ⟨hkb, hnoext0, hwf5, hal5⟩ := scratch_word hmem halign 5
  obtain ⟨hhash, hnoext, -, -⟩ := scratch_mapSlot hwf5 hal5 target 4
  unfold t_0a16_c32 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_add s1
  rw [show (3 : B256) + Bytes.toB256 [2] = 5 from rfl] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_dup (w := Bytes.toB256 [1]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_dup (w := b.getStorVal sevm.currentTarget 5) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_dup (w := Bytes.toB256 [32]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    hkb, hnoext0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_dup (w := b.getStorVal sevm.currentTarget 5 +
    (5 : B256).toBytes.keccak) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_and s1
  rw [hiMask_eq] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_dup (w := target) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_and s1
  rw [mask_and_canonical htarget] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_dup (w := target) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_or s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G35, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G37, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G39, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_dup (w := (0 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G41, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G42, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G43, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G44, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G45, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G46, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G47, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G48, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G49, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G50, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (3 : B256) + Bytes.toB256 [1] = 4 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl, hhash, hnoext] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G51, rfl⟩ := ri_sstore hfork s1
  refine ⟨_, G51, ?_, run⟩
  refine StorStep.congr (StorStep.of_getStor (fun a ha => ?_) ?_) ?_
  · simp only [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]
  · simp only [afterSstore_logs, afterSload_logs]
  · simp only [getStorVal_eq_getStor, afterSstore_getStor_self, afterSload_getStor, pushStor]
    rfl

/-- The absent-target prefix shared by the fresh and absent-zero branches: the
target guard, the assignment rewrite (the old pauser reads zero), and the
push block, up to entry 4, with the world effect named. -/
theorem absentPrefix_inv {newPauser target : B256} {ra : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (htarget : nonzeroCanonicalAddress target) (hnew : canonicalAddress newPauser)
    (hassign : addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) = 0)
    (run : SFunc.Run prog sevm (St b (newPauser :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    ∃ b2 M2 G2, StorStep sevm b b2
        (pushStor ((Devm.getStor b sevm.currentTarget).set (mapSlot target 3)
          (addressSlotWriteWord ((Devm.getStor b sevm.currentTarget).get (mapSlot target 3))
            newPauser)) target) ∧
      Mem.Wf M2 ∧ M2.size % 32 = 0 ∧
      SFunc.RunCut prog sevm [] (St b2 (0 :: newPauser :: target :: 3 :: ra :: base) M2 G2)
        t_0a81_c4 (.done (.returned post)) := by
  obtain ⟨G1, run⟩ := entry32_target_guard_inv htarget run
  obtain ⟨G2, ⟨hne, -⟩ | ⟨-, run⟩⟩ :=
    entry32_assignment_split hfork htarget.2 hmem halign hnew run
  · exact absurd hassign hne
  rw [hassign] at run
  obtain ⟨-, -, hwf1, hal1⟩ := scratch_mapSlot hmem halign target 3
  obtain ⟨b2, G3, h2, run⟩ := t0a16_inv hfork htarget.2 hwf1 hal1 run
  obtain ⟨-, -, hwf5, hal5⟩ := scratch_word hwf1 hal1 5
  obtain ⟨-, -, hwf2, hal2⟩ := scratch_mapSlot hwf5 hal5 target 4
  refine ⟨b2, _, G3, ?_, hwf2, hal2, run⟩
  have h1 := ((StorStep.refl sevm b).sload (mapSlot target 3)).sstore (mapSlot target 3)
    (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) newPauser)
  exact h1.trans (h2.congr (by rw [h1.self]; rfl))

/-! ## The fresh branch's storage, against `rawFreshPost` -/

/-- The five logical keys `rawFreshPost`'s writes touch (exactly
`logicalFreshPost`'s write list): the fresh branch's instance of the unified
`RegistryKeysFaithful` premise ranges over these, at bound `length + 1`. -/
def freshWriteKeys (entries : List LidoCircuitBreaker.Entry) (target newPauser : B256) :
    List B256 :=
  [assignmentSlot target, arrayEntrySlot (Nat.toB256 (entries.length + 1)), indexSlot target,
    arrayLengthSlot, countSlot newPauser]

theorem freshStor_eq_rawFreshPost
    {raw : Stor} {entries : List LidoCircuitBreaker.Entry} {target newPauser : B256}
    (hw : RegistryWitness (solRegistryStorage raw) entries)
    (htarget : nonzeroCanonicalAddress target) (hnew : nonzeroCanonicalAddress newPauser)
    (hfaithful : RegistryKeysFaithful (entries.length + 1)
      (freshWriteKeys entries target newPauser)) (key : B256) :
    ((pushStor (raw.set (mapSlot target 3)
        (addressSlotWriteWord (raw.get (mapSlot target 3)) newPauser)) target).set
      (mapSlot newPauser 6) (1 + (pushStor (raw.set (mapSlot target 3)
        (addressSlotWriteWord (raw.get (mapSlot target 3)) newPauser)) target).get
          (mapSlot newPauser 6))).get key =
      (rawFreshPost raw entries target newPauser).get key := by
  have hlenLt := hw.fresh_length_lt_2pow252
  have hlen : raw.get 5 = Nat.toB256 entries.length := by
    have h := hw.lengthWord
    rw [solRegistryStorage_length] at h
    exact h
  have hcountNew : raw.get (mapSlot newPauser 6) =
      Nat.toB256 (assignmentCount entries newPauser) := by
    have h := hw.counts newPauser hnew.2
    rw [solRegistryStorage_count _ _ hnew.2] at h
    exact h
  have harrKey : solKey (arrayEntrySlot (Nat.toB256 (entries.length + 1))) =
      registryArraySlot entries.length := solKey_arrayEntrySlot hlenLt
  have hLb : (Nat.toB256 (entries.length + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt (by omega)]
    exact hlenLt
  have hobsA : RegistryObservable (entries.length + 1) (assignmentSlot target) :=
    Or.inl ⟨target, htarget.2, rfl⟩
  have hobsE : RegistryObservable (entries.length + 1)
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length, by omega, rfl⟩)))
  have hmemLen : arrayLengthSlot ∈ freshWriteKeys entries target newPauser := by
    simp only [freshWriteKeys, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have hmemCnt : countSlot newPauser ∈ freshWriteKeys entries target newPauser := by
    simp only [freshWriteKeys, List.mem_cons, List.not_mem_nil, or_false, or_true]
  have h35 : mapSlot target 3 ≠ 5 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful hmemLen hobsA
      (registryAddressFamilies_ne_arrayLengthSlot htarget.2 hnew.2).1
  have h3c : mapSlot target 3 ≠ mapSlot newPauser 6 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_countSlot hnew.2]
    exact solKey_ne_of_faithful hfaithful hmemCnt hobsA
      (registryAddressFamilies_pairwise htarget.2 htarget.2 hnew.2).2.1
  have h5c : (5 : B256) ≠ mapSlot newPauser 6 := by
    rw [← solKey_arrayLengthSlot, ← solKey_countSlot hnew.2]
    exact solKey_ne_of_faithful hfaithful hmemCnt (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (registryAddressFamilies_ne_arrayLengthSlot htarget.2 hnew.2).2.2.symm
  have he5 : registryArraySlot entries.length ≠ 5 := by
    rw [← harrKey, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful hmemLen hobsE
      (arrayEntrySlot_ne_arrayLengthSlot hlenLt)
  have hec : registryArraySlot entries.length ≠ mapSlot newPauser 6 := by
    rw [← harrKey, ← solKey_countSlot hnew.2]
    exact solKey_ne_of_faithful hfaithful hmemCnt hobsE
      (registryAddressFamilies_ne_arrayEntrySlot htarget.2 hnew.2 hLb).2.2.symm
  have h4c : mapSlot target 4 ≠ mapSlot newPauser 6 := by
    rw [← solKey_indexSlot htarget.2, ← solKey_countSlot hnew.2]
    exact solKey_ne_of_faithful hfaithful hmemCnt (Or.inr (Or.inl ⟨target, htarget.2, rfl⟩))
      (registryAddressFamilies_pairwise htarget.2 htarget.2 hnew.2).2.2
  have hRA : ∀ i, registryArraySlot i = registryArrayBase + Nat.toB256 i := fun _ => rfl
  have hsucc : Nat.toB256 entries.length + 1 = Nat.toB256 (entries.length + 1) :=
    (natToB256_succ_eq_add_one _ (by omega)).symm
  have he : Nat.toB256 entries.length + registryArrayBase =
      registryArraySlot entries.length := by
    rw [hRA, B256.add_comm]
  have hcntLe := assignmentCount_le_length entries newPauser
  simp only [pushStor, Stor.get_set_ne _ h35, hlen, hsucc, he, Stor.get_set_ne _ he5,
    Stor.get_set_self, Stor.get_set_ne _ h4c, Stor.get_set_ne _ hec, Stor.get_set_ne _ h5c,
    Stor.get_set_ne _ h3c, hcountNew,
    one_add_natToB256 (by omega : assignmentCount entries newPauser + 1 < 2 ^ 256),
    rawFreshPost, Stor.get_set_ite]
  have h5e : ¬ ((5 : B256) = registryArraySlot entries.length) := fun h => he5 h.symm
  simp only [h5e, ite_false, addressSlotWriteWord]
  rw [B256.or_comm target]
  by_cases hk5 : (5 : B256) = key
  · subst hk5
    have hc5 : ¬ (mapSlot newPauser 6 = 5) := fun h => h5c h.symm
    simp only [hc5, he5, ite_false, ite_true]
    split_ifs <;> rfl
  · simp only [hk5, ite_false]

end Blocks

/-! ## The fresh branch -/

/-- Every successful run of `setPauser` (entry 32) on an absent target with a
nonzero new pauser returns to its caller's `base` stack, having emitted the
`PauserSet` log (previous pauser zero), with the contract's storage pointwise
equal to `rawFreshPost` (the `writes` field of `RawFreshReadEffect`) and every
other account's storage unchanged.  The bytecode stores the length before the
new element and index; the pointwise equality absorbs the reorder through the
branch's own `RegistryKeysFaithful` instance over `freshWriteKeys`. -/
theorem setPauser_fresh_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {newPauser target : B256} {ra : B256} {base : List B256} {post : Devm}
    {entries : List LidoCircuitBreaker.Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (htarget : nonzeroCanonicalAddress target) (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = none)
    (hfaithful : RegistryKeysFaithful (entries.length + 1)
      (freshWriteKeys entries target newPauser))
    (run : SFunc.Run prog sevm (St b (newPauser :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    (∀ key, (Devm.getStor post sevm.currentTarget).get key =
      (rawFreshPost (Devm.getStor b sevm.currentTarget) entries target newPauser).get key) ∧
    (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor b a) ∧
    ∃ (b' : Devm) (data : Bytes) (M' : Mem) (G' : Nat), post = St (b'.addLog
      ⟨sevm.currentTarget, [pauserSetTopic, target, 0, newPauser], data⟩) base M' G' ∧
      b'.logs = b.logs := by
  have hzero : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num only
  have hassign : addressSlotReadWord
      (b.getStorVal sevm.currentTarget (mapSlot target 3)) = 0 := by
    have h := hw.assignments target htarget.2
    rw [solRegistryStorage_assignment _ _ htarget.2, findEntry_none_assignmentAt hfind] at h
    exact h
  obtain ⟨b2, M2, G2, h2, hwf2, hal2, run⟩ :=
    absentPrefix_inv hfork hmem halign htarget hnew.2 hassign run
  rcases entry4_inv hnew.2 run with ⟨-, G4, run⟩ | ⟨h0, -⟩
  swap
  · exact absurd h0 hnew.1
  obtain ⟨-, G5, run⟩ := t0a9e_inv hfork hnew.2 hwf2 hal2 run
  obtain ⟨data, M', G6, rfl⟩ := entry5_inv hzero hnew.2 htarget.2 run
  have h := h2.trans (((StorStep.refl sevm b2).sload (mapSlot newPauser 6)).sstore
    (mapSlot newPauser 6) (1 + b2.getStorVal sevm.currentTarget (mapSlot newPauser 6)))
  refine ⟨fun key => ?_, fun a ha => ?_, _, data, M', G6, rfl, h.logs⟩
  · rw [getStor_St_addLog, h.self, h2.getStorVal, h2.self]
    exact freshStor_eq_rawFreshPost hw htarget hnew hfaithful key
  · rw [getStor_St_addLog, h.other a ha]

/-! ## The absent-zero branch (push, then swap-and-pop) -/

theorem absentZeroStor_eq_rawAbsentZeroPost
    {raw : Stor} {entries : List LidoCircuitBreaker.Entry} {target : B256}
    (hw : RegistryWitness (solRegistryStorage raw) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfaithful : RegistryKeysFaithful (entries.length + 1)
      ((absentZeroWrites entries target).map Prod.fst)) :
    (∀ key, (removalTailStor (pushStor (raw.set (mapSlot target 3)
        (addressSlotWriteWord (raw.get (mapSlot target 3)) 0)) target) target).get key =
      (rawAbsentZeroPost raw entries target).get key) ∧
    addressSlotReadWord ((pushStor (raw.set (mapSlot target 3)
        (addressSlotWriteWord (raw.get (mapSlot target 3)) 0)) target).get
      (registryArrayBase + ((pushStor (raw.set (mapSlot target 3)
        (addressSlotWriteWord (raw.get (mapSlot target 3)) 0)) target).get 5 - 1))) =
      target := by
  have hlenLt := hw.fresh_length_lt_2pow252
  have hlen : raw.get 5 = Nat.toB256 entries.length := by
    have h := hw.lengthWord
    rw [solRegistryStorage_length] at h
    exact h
  have harrKey : solKey (arrayEntrySlot (Nat.toB256 (entries.length + 1))) =
      registryArraySlot entries.length := solKey_arrayEntrySlot hlenLt
  have hLb : (Nat.toB256 (entries.length + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt (by omega)]
    exact hlenLt
  have hkeys : ∀ k, k = assignmentSlot target ∨ k = indexSlot target ∨ k = arrayLengthSlot ∨
      k = arrayEntrySlot (Nat.toB256 (entries.length + 1)) →
      k ∈ (absentZeroWrites entries target).map Prod.fst := by
    rintro k (rfl | rfl | rfl | rfl) <;> simp only [absentZeroWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, or_self]
  have hobsE : RegistryObservable (entries.length + 1)
      (arrayEntrySlot (Nat.toB256 (entries.length + 1))) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length, by omega, rfl⟩)))
  have hobsI : RegistryObservable (entries.length + 1) (indexSlot target) :=
    Or.inr (Or.inl ⟨target, htarget.2, rfl⟩)
  have h35 : mapSlot target 3 ≠ 5 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful (hkeys _ (.inr (.inr (.inl rfl))))
      (Or.inl ⟨target, htarget.2, rfl⟩)
      (registryAddressFamilies_ne_arrayLengthSlot htarget.2 htarget.2).1
  have h45 : mapSlot target 4 ≠ 5 := by
    rw [← solKey_indexSlot htarget.2, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful (hkeys _ (.inr (.inr (.inl rfl)))) hobsI
      (registryAddressFamilies_ne_arrayLengthSlot htarget.2 htarget.2).2.1
  have he5 : registryArraySlot entries.length ≠ 5 := by
    rw [← harrKey, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful (hkeys _ (.inr (.inr (.inl rfl)))) hobsE
      (arrayEntrySlot_ne_arrayLengthSlot hlenLt)
  have h4e : mapSlot target 4 ≠ registryArraySlot entries.length := by
    rw [← solKey_indexSlot htarget.2, ← harrKey]
    exact solKey_ne_of_faithful hfaithful (hkeys _ (.inr (.inr (.inr rfl)))) hobsI
      (registryAddressFamilies_ne_arrayEntrySlot htarget.2 htarget.2 hLb).2.1
  have hRA : ∀ i, registryArraySlot i = registryArrayBase + Nat.toB256 i := fun _ => rfl
  have hsucc : Nat.toB256 entries.length + 1 = Nat.toB256 (entries.length + 1) :=
    (natToB256_succ_eq_add_one _ (by omega)).symm
  have hpred : Nat.toB256 (entries.length + 1) - 1 = Nat.toB256 entries.length := by
    simpa only [add_tsub_cancel_right] using
      (natToB256_pred_eq_sub_one (entries.length + 1) (by omega) (by omega)).symm
  have he : Nat.toB256 entries.length + registryArrayBase =
      registryArraySlot entries.length := by
    rw [hRA, B256.add_comm]
  have htail := ffWord_add_length_base (L := entries.length + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at htail
  have hnewLen : Nat.toB256 (entries.length + 1) + ffWord = Nat.toB256 entries.length := by
    rw [B256.add_comm, ffWord_add_natToB256 (by omega) (by omega), Nat.add_sub_cancel]
  have hclean : addressSlotReadWord target = target :=
    addressSlotReadWord_eq_self_of_lt htarget.2
  have hX : ∀ w, target ||| addressMask &&& w = addressSlotWriteWord w target := fun w =>
    B256.or_comm _ _
  constructor
  · intro key
    simp only [removalTailStor, pushStor, Stor.get_set_ne _ h35, hlen, hsucc, he,
      Stor.get_set_ne _ h45, Stor.get_set_ne _ he5, Stor.get_set_self,
      Stor.get_set_ne _ h4e, hpred, ← hRA, hX, addressSlotReadWord_write_of_clean _ _ hclean,
      htail, hnewLen]
    simp only [rawAbsentZeroPost, applyRegistryRawWrites, absentZeroWrites, List.foldl,
      solKey_assignmentSlot htarget.2, solKey_indexSlot htarget.2, solKey_arrayLengthSlot,
      harrKey, registryRawValue_assignmentSlot htarget.2,
      registryRawValue_indexSlot htarget.2, registryRawValue_arrayLengthSlot,
      registryRawValue_arrayEntrySlot hlenLt, Stor.get_set_ite]
    have h5e : ¬ ((5 : B256) = registryArraySlot entries.length) := fun h => he5 h.symm
    have hclr : ∀ w, addressMask &&& addressSlotWriteWord w target = addressMask &&& w :=
      fun w => addressMask_and_write_of_clean w target
        (addressMask_and_eq_zero_of_lt htarget.2)
    have hclr0 : ∀ w, addressSlotWriteWord w 0 = addressMask &&& w := fun w => B256.or_zero _
    simp only [h5e, h4e, ite_true, ite_false, hclr0, hclr]
    by_cases h1 : mapSlot target 4 = key
    · simp only [h1, ite_true]
    by_cases h2 : (5 : B256) = key
    · simp only [h1, h2, ite_true, ite_false]
    by_cases h3 : registryArraySlot entries.length = key
    · simp only [h1, h2, h3, ite_true, ite_false]
    · simp only [h1, h2, h3, ite_false]
  · simp only [pushStor, Stor.get_set_ne _ h35, hlen, hsucc, he, Stor.get_set_ne _ h45,
      Stor.get_set_ne _ he5, Stor.get_set_self, Stor.get_set_ne _ h4e, hpred, ← hRA, hX,
      addressSlotReadWord_write_of_clean _ _ hclean]

/-- Every successful run of `setPauser` (entry 32) on an absent target with a
zero new pauser (push, then immediate swap-and-pop) returns to its caller's
`base` stack, having emitted the `PauserSet` log (both pausers zero), with
the contract's storage pointwise equal to `rawAbsentZeroPost` (the exact
`hwrites` shape of `rawAbsentZero_preservesRegistry`) and every other
account's storage unchanged. -/
theorem setPauser_absentZero_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {target : B256} {ra : B256} {base : List B256} {post : Devm}
    {entries : List LidoCircuitBreaker.Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = none)
    (hfaithful : RegistryKeysFaithful (entries.length + 1)
      ((absentZeroWrites entries target).map Prod.fst))
    (run : SFunc.Run prog sevm (St b (0 :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    (∀ key, (Devm.getStor post sevm.currentTarget).get key =
      (rawAbsentZeroPost (Devm.getStor b sevm.currentTarget) entries target).get key) ∧
    (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor b a) ∧
    ∃ (b' : Devm) (data : Bytes) (M' : Mem) (G' : Nat), post = St (b'.addLog
      ⟨sevm.currentTarget, [pauserSetTopic, target, 0, 0], data⟩) base M' G' ∧
      b'.logs = b.logs := by
  have hzero : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num only
  have hassign : addressSlotReadWord
      (b.getStorVal sevm.currentTarget (mapSlot target 3)) = 0 := by
    have h := hw.assignments target htarget.2
    rw [solRegistryStorage_assignment _ _ htarget.2, findEntry_none_assignmentAt hfind] at h
    exact h
  obtain ⟨b2, M2, G2, h2, hwf2, hal2, run⟩ :=
    absentPrefix_inv hfork hmem halign htarget hzero hassign run
  rcases entry4_inv hzero run with ⟨hne, -⟩ | ⟨-, G4, run⟩
  · exact absurd rfl hne
  obtain ⟨hEq, hlastEq⟩ := absentZeroStor_eq_rawAbsentZeroPost hw htarget hfaithful
  have hlast : canonicalAddress (addressSlotReadWord ((Devm.getStor b2 sevm.currentTarget).get
      (registryArrayBase + (b2.getStorVal sevm.currentTarget 5 - 1)))) := by
    rw [h2.getStorVal, h2.self]
    exact (congrArg canonicalAddress hlastEq).mpr htarget.2
  obtain ⟨b', data, M', G', rfl, h6⟩ :=
    removalArm_inv hfork htarget.2 hzero hlast hwf2 hal2 run
  have h := h2.trans h6
  rw [h2.self] at h
  refine ⟨fun key => ?_, fun a ha => ?_, b', data, M', G', rfl, h.logs⟩
  · rw [getStor_St_addLog, h.self]
    exact hEq key
  · rw [getStor_St_addLog, h.other a ha]

end Blanc.Lift.LidoCircuitBreakerDeployed
