import Blanc.Lift.LidoCircuitBreakerDeployed.Removal
import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserCalls
import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryLayout

/-! Inversion of `Registry.setPauser`'s found-target, nonzero-new-pauser run
on the exact deployed CircuitBreaker bytecode: the old pauser's count
decrement (`t_09da_c32` with entry 40), entry 4's `newPauser` test, the new
pauser's count increment (`t_0a9e_c4` with entry 24), then entry 5. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.LidoCircuitBreaker

section Blocks

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}

/-- `t_09da_c32`: the old pauser's count slot is read, decremented through
entry 40 (whose zero arm reverts), written back, and control joins entry 4
with the caller's stack. -/
theorem t09da_inv {oldP newP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hold : canonicalAddress oldP)
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (oldP :: newP :: target :: 3 :: R :: base) M G)
      t_09da_c32 (.done (.returned post))) :
    b.getStorVal sevm.currentTarget (mapSlot oldP 6) ≠ 0 ∧
    ∃ G', SFunc.RunCut prog sevm []
      (St (afterSstore sevm (afterSload sevm b (mapSlot oldP 6)) (mapSlot oldP 6)
          (ffWord + b.getStorVal sevm.currentTarget (mapSlot oldP 6)))
        (oldP :: newP :: target :: 3 :: R :: base)
        ((M.write 0 oldP.toBytes).write 32 (6 : B256).toBytes) G')
      t_0a81_c4 (.done (.returned post)) := by
  obtain ⟨hhash, hnoext, -, -⟩ := scratch_mapSlot hmem halign oldP 6
  unfold t_09da_c32 at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_dup (w := oldP) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_and s1
  rw [mask_and_canonical hold] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (3 : B256) + Bytes.toB256 [3] = 6 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl,
    hhash, hnoext] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_dup (w := mapSlot oldP 6) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_push s1
  obtain ⟨G24, ⟨D, callee, run⟩ | ⟨D, -, hr⟩⟩ := ric_call entry40_lookup run
  · obtain ⟨hnz, G25, rfl⟩ := entry40_returned_inv callee
    refine ⟨hnz, ?_⟩
    unfold t_0a0d_c32 at run
    obtain ⟨G26, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G27, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G28, rfl⟩ := ri_swap (n := 1) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G29, rfl⟩ := ri_sstore hfork s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G30, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G31, rfl⟩ := ri_push s1
    obtain ⟨G32, run⟩ := ric_jump (List.not_mem_nil) entry4_lookup run
    exact ⟨G32, run⟩
  · cases hr

/-- Entry 4 tests the (canonical) new pauser: nonzero continues at the
count-increment block `t_0a9e_c4`, zero at the removal block `t_0ada_c4`. -/
theorem entry4_inv {oldP newP target R : B256} {base : List B256} {post : Devm}
    (hnew : canonicalAddress newP)
    (run : SFunc.RunCut prog sevm []
      (St b (oldP :: newP :: target :: 3 :: R :: base) M G)
      t_0a81_c4 (.done (.returned post))) :
    (newP ≠ 0 ∧ ∃ G', SFunc.RunCut prog sevm []
      (St b (oldP :: newP :: target :: 3 :: R :: base) M G')
      t_0a9e_c4 (.done (.returned post))) ∨
    (newP = 0 ∧ ∃ G', SFunc.RunCut prog sevm []
      (St b (oldP :: newP :: target :: 3 :: R :: base) M G')
      t_0ada_c4 (.done (.returned post))) := by
  unfold t_0a81_c4 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := newP) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_and s1
  rw [mask_and_canonical hnew] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G7, run⟩ | ⟨hnz, G7, run⟩
  · refine .inl ⟨?_, G7, run⟩
    rintro rfl
    exact absurd hz (by decide)
  · exact .inr ⟨eq_zero_of_iszero_ne_zero hnz, G7, run⟩

/-- `t_0a9e_c4`: the new pauser's count slot is read, incremented through
entry 24 (whose overflow arm reverts), written back, and control joins
entry 5 with the caller's stack. -/
theorem t0a9e_inv {oldP newP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hnew : canonicalAddress newP)
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (oldP :: newP :: target :: 3 :: R :: base) M G)
      t_0a9e_c4 (.done (.returned post))) :
    b.getStorVal sevm.currentTarget (mapSlot newP 6) - ffWord ≠ 0 ∧
    ∃ G', SFunc.RunCut prog sevm []
      (St (afterSstore sevm (afterSload sevm b (mapSlot newP 6)) (mapSlot newP 6)
          (1 + b.getStorVal sevm.currentTarget (mapSlot newP 6)))
        (oldP :: newP :: target :: 3 :: R :: base)
        ((M.write 0 newP.toBytes).write 32 (6 : B256).toBytes) G')
      t_0c5e_c5 (.done (.returned post)) := by
  obtain ⟨hhash, hnoext, -, -⟩ := scratch_mapSlot hmem halign newP 6
  unfold t_0a9e_c4 at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_dup (w := newP) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_and s1
  rw [mask_and_canonical hnew] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (3 : B256) + Bytes.toB256 [3] = 6 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl,
    hhash, hnoext] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_dup (w := mapSlot newP 6) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_push s1
  obtain ⟨G24, ⟨D, callee, run⟩ | ⟨D, -, hr⟩⟩ := ric_call entry24_lookup run
  · obtain ⟨hnz, G25, rfl⟩ := entry24_returned_inv callee
    refine ⟨hnz, ?_⟩
    unfold t_0ad1_c4 at run
    obtain ⟨G26, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G27, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G28, rfl⟩ := ri_swap (n := 1) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G29, rfl⟩ := ri_sstore hfork s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G30, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G31, rfl⟩ := ri_push s1
    obtain ⟨G32, run⟩ := ric_jump (List.not_mem_nil) entry5_lookup run
    exact ⟨G32, run⟩
  · cases hr

/-! ## Raw-value and key facts the branch theorems share -/

theorem getStor_St_addLog (d : Devm) (L : Log) (S : List B256) (M : Mem) (G : Nat) (a : Adr) :
    Devm.getStor (St (d.addLog L) S M G) a = Devm.getStor d a := rfl

/-- The checked decrement's `ff..ff + x` is `x - 1`. -/
theorem ffWord_add (x : B256) : ffWord + x = x - 1 := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_sub,
    show ffWord.toNat = 2 ^ 256 - 1 from by decide,
    show (1 : B256).toNat = 1 from rfl]
  have := B256.toNat_lt x
  congr 1
  omega

theorem ffWord_add_natToB256 {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 256) :
    ffWord + Nat.toB256 n = Nat.toB256 (n - 1) := by
  rw [ffWord_add, natToB256_pred_eq_sub_one n hpos hlt]

theorem one_add_natToB256 {n : Nat} (hlt : n + 1 < 2 ^ 256) :
    1 + Nat.toB256 n = Nat.toB256 (n + 1) := by
  rw [B256.add_comm, natToB256_succ_eq_add_one n hlt]

/-- A key observed by a witness and distinct from a faithfully written key
occupies a different raw slot. -/
theorem solKey_ne_of_faithful {bound : Nat} {T : List B256} {t k : B256}
    (hf : RegistryKeysFaithful bound T) (ht : t ∈ T) (hk : RegistryObservable bound k)
    (hne : k ≠ t) : solKey k ≠ solKey t :=
  fun h => hne (hf t ht k hk h)

/-! ## The found-target, nonzero-new-pauser branch -/

/-- The deployed existing-target update needs three pre-state reads and
three finite raw-slot comparisons. No all-address registry witness is required. -/
theorem setPauser_nonzero_inv_of_reads {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {newPauser target : B256} {ra : B256} {base : List B256} {post : Devm}
    {entries : List LidoCircuitBreaker.Entry} {index : Nat} {oldPauser : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (htarget : nonzeroCanonicalAddress target) (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hold : nonzeroCanonicalAddress oldPauser)
    (hlenLt : entries.length < 2 ^ 252)
    (hassign : addressSlotReadWord
      (b.getStorVal sevm.currentTarget (mapSlot target 3)) = oldPauser)
    (hcountOld : b.getStorVal sevm.currentTarget (mapSlot oldPauser 6) =
      Nat.toB256 (assignmentCount entries oldPauser))
    (hcountNew : b.getStorVal sevm.currentTarget (mapSlot newPauser 6) =
      Nat.toB256 (assignmentCount entries newPauser))
    (hk3c6 : mapSlot target 3 ≠ mapSlot oldPauser 6)
    (hk3cN : mapSlot target 3 ≠ mapSlot newPauser 6)
    (hcountsApart : oldPauser ≠ newPauser → mapSlot oldPauser 6 ≠ mapSlot newPauser 6)
    (run : SFunc.Run prog sevm (St b (newPauser :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    (∀ key, (Devm.getStor post sevm.currentTarget).get key =
      (rawNonzeroPost (Devm.getStor b sevm.currentTarget) entries target newPauser
        oldPauser).get key) ∧
    (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor b a) ∧
    ∃ (b' : Devm) (data : Bytes) (M' : Mem) (G' : Nat), post = St (b'.addLog
      ⟨sevm.currentTarget, [pauserSetTopic, target, oldPauser, newPauser], data⟩) base M' G' ∧
      b'.logs = b.logs := by
  -- The walk.
  obtain ⟨G1, run⟩ := entry32_target_guard_inv htarget run
  obtain ⟨G2, run⟩ := entry32_assignment_inv hfork htarget.2 hmem halign hnew.2
    (by rw [hassign]; exact hold.1) run
  rw [hassign] at run
  obtain ⟨-, -, hwf1, hal1⟩ := scratch_mapSlot hmem halign target 3
  obtain ⟨-, G3, run⟩ := t09da_inv hfork hold.2 hwf1 hal1 run
  obtain ⟨-, -, hwf2, hal2⟩ := scratch_mapSlot hwf1 hal1 oldPauser 6
  rcases entry4_inv hnew.2 run with ⟨-, G4, run⟩ | ⟨h0, -⟩
  swap
  · exact absurd h0 hnew.1
  obtain ⟨-, G5, run⟩ := t0a9e_inv hfork hnew.2 hwf2 hal2 run
  obtain ⟨data, M', G6, rfl⟩ := entry5_inv hold.2 hnew.2 htarget.2 run
  refine ⟨?_, ?_, _, data, M', G6, rfl, ?_⟩
  · intro key
    rw [getStor_St_addLog, getStor_afterStore, getStorVal_afterStore, getStor_afterStore, getStorVal_afterStore,
      getStor_afterStore]
    have hc6 : ((Devm.getStor b sevm.currentTarget).set (mapSlot target 3)
        (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3))
          newPauser)).get (mapSlot oldPauser 6) =
        Nat.toB256 (assignmentCount entries oldPauser) := by
      rw [Stor.get_set_ne _ hk3c6]
      exact hcountOld
    have hpos := assignmentCount_pos_of_findEntry hfind
    have hltOld : assignmentCount entries oldPauser < 2 ^ 256 := by
      have := assignmentCount_le_length entries oldPauser
      omega
    have hcntLe := assignmentCount_le_length entries newPauser
    rw [hc6, ffWord_add_natToB256 hpos hltOld]
    have hcN : (((Devm.getStor b sevm.currentTarget).set (mapSlot target 3)
        (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3))
          newPauser)).set (mapSlot oldPauser 6)
          (Nat.toB256 (assignmentCount entries oldPauser - 1))).get (mapSlot newPauser 6) =
        Nat.toB256 (assignmentCount entries newPauser -
          (if oldPauser = newPauser then 1 else 0)) := by
      by_cases heq : oldPauser = newPauser
      · subst heq
        simp only [ite_true, Stor.get_set_self]
      · have hc6cN : mapSlot oldPauser 6 ≠ mapSlot newPauser 6 := by
          exact hcountsApart heq
        rw [Stor.get_set_ne _ hc6cN, Stor.get_set_ne _ hk3cN]
        simp only [heq, ite_false, Nat.sub_zero]
        exact hcountNew
    rw [hcN, one_add_natToB256 (by omega)]
    simp only [rawNonzeroPost, applyRegistryRawWrites, nonzeroWrites, List.foldl,
      solKey_assignmentSlot htarget.2, solKey_countSlot hold.2, solKey_countSlot hnew.2,
      registryRawValue_assignmentSlot htarget.2, registryRawValue_countSlot hold.2,
      registryRawValue_countSlot hnew.2]
    rfl
  · intro a ha
    rw [getStor_St_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha, getStor_afterStore_ne ha]
  · rw [logs_afterStore, logs_afterStore, logs_afterStore]

/-- Every successful run of `setPauser` (entry 32) on a found target with a
nonzero new pauser returns to its caller's `base` stack, having emitted the
`PauserSet` log, with the contract's storage pointwise equal to
`rawNonzeroPost` and every other account's storage unchanged. -/
theorem setPauser_nonzero_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {newPauser target : B256} {ra : B256} {base : List B256} {post : Devm}
    {entries : List LidoCircuitBreaker.Entry} {index : Nat} {oldPauser : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (htarget : nonzeroCanonicalAddress target) (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      ((nonzeroWrites entries target newPauser oldPauser).map Prod.fst))
    (run : SFunc.Run prog sevm (St b (newPauser :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    (∀ key, (Devm.getStor post sevm.currentTarget).get key =
      (rawNonzeroPost (Devm.getStor b sevm.currentTarget) entries target newPauser
        oldPauser).get key) ∧
    (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor b a) ∧
    ∃ (b' : Devm) (data : Bytes) (M' : Mem) (G' : Nat), post = St (b'.addLog
      ⟨sevm.currentTarget, [pauserSetTopic, target, oldPauser, newPauser], data⟩) base M' G' ∧
      b'.logs = b.logs := by
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hassign : addressSlotReadWord
      (b.getStorVal sevm.currentTarget (mapSlot target 3)) = oldPauser := by
    have h := hw.assignments target htarget.2
    rw [solRegistryStorage_assignment _ _ htarget.2, findEntry_assignmentAt hfind] at h
    exact h
  have hcountOld : b.getStorVal sevm.currentTarget (mapSlot oldPauser 6) =
      Nat.toB256 (assignmentCount entries oldPauser) := by
    have h := hw.counts oldPauser hold.2
    rw [solRegistryStorage_count _ _ hold.2] at h
    exact h
  have hcountNew : b.getStorVal sevm.currentTarget (mapSlot newPauser 6) =
      Nat.toB256 (assignmentCount entries newPauser) := by
    have h := hw.counts newPauser hnew.2
    rw [solRegistryStorage_count _ _ hnew.2] at h
    exact h
  -- Raw slot separations, from the faithful premise.
  have hmemT : ∀ t, t = assignmentSlot target ∨ t = countSlot oldPauser ∨
      t = countSlot newPauser → t ∈ (nonzeroWrites entries target newPauser oldPauser).map
        Prod.fst := by
    rintro t (rfl | rfl | rfl) <;> simp only [nonzeroWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  have hk3c6 : mapSlot target 3 ≠ mapSlot oldPauser 6 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_countSlot hold.2]
    exact solKey_ne_of_faithful hfaithful (hmemT _ (.inr (.inl rfl)))
      (Or.inl ⟨target, htarget.2, rfl⟩)
      (registryAddressFamilies_pairwise htarget.2 htarget.2 hold.2).2.1
  have hk3cN : mapSlot target 3 ≠ mapSlot newPauser 6 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_countSlot hnew.2]
    exact solKey_ne_of_faithful hfaithful (hmemT _ (.inr (.inr rfl)))
      (Or.inl ⟨target, htarget.2, rfl⟩)
      (registryAddressFamilies_pairwise htarget.2 htarget.2 hnew.2).2.1
  have hcountsApart : oldPauser ≠ newPauser → mapSlot oldPauser 6 ≠ mapSlot newPauser 6 := by
    intro hne
    rw [← solKey_countSlot hold.2, ← solKey_countSlot hnew.2]
    refine solKey_ne_of_faithful hfaithful (hmemT _ (.inr (.inr rfl)))
      (Or.inr (Or.inr (Or.inl ⟨oldPauser, hold.2, rfl⟩))) ?_
    intro h
    exact hne (countSlot_injective hold.2 hnew.2 h)
  exact setPauser_nonzero_inv_of_reads hfork hmem halign htarget hnew hfind hold
    hw.entries_length_lt_2pow252 hassign hcountOld hcountNew hk3c6 hk3cN hcountsApart run

end Blocks

end Blanc.Lift.LidoCircuitBreakerDeployed
