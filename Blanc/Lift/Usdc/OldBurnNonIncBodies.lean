import Blanc.Lift.ObservedReachSplit
import Blanc.Lift.Usdc.OldBurnNonIncCallees

/-! V2 and V2_1 burn stores are bounded at each original store's own pre-state. -/
namespace Blanc.Lift.Usdc.OldBurnNonIncBodies

open Jaune Blanc Blanc.Lift

/-- Both older final tails write the bounded caller-balance value. -/
theorem tail_source {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: S) M G, ModernBurnStores.callerTail version, K⟩ T)
    (bounded : value.toNat ≤
      (b.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  obtain ⟨⟨rest, stack⟩, unchanged, hash⟩ := ModernBurnStores.caller_store_source old erase run hT cont
  refine ⟨_, _, rest, stack, ?_, .inr ⟨sevm.caller, rfl, hash⟩⟩
  rw [unchanged]
  exact bounded

/-- Original nonincrease API, projected from the stronger observed source. -/
theorem tail_nonInc {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q version.cert.prog sevm
      ⟨St b (value :: S) M G, ModernBurnStores.callerTail version, K⟩ T)
    (bounded : value.toNat ≤
      (b.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := tail_source old erase (ObservedReach.of_reach run) bounded hT cont
  exact ⟨key, value, rest, stack, bound⟩

def supplyStart : ModernVersion → SFunc
  | .v2 => ImplV2.t_2392_c45
  | .v2_1 => ImplV2_1.t_2308_c47
  | .v2_2 => .ret

/-- The supply write and subsequent balance write remain non-increasing under key aliasing. -/
theorem stores_source {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {balance saved amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (balance :: saved :: amount :: S) M G, supplyStart version, K⟩ T)
    (bounded : balance.toNat ≤
      (b.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    simp only [supplyStart] at run
    first | unfold ImplV2.t_2392_c45 at run | unfold ImplV2_1.t_2308_c47 at run
    orsd
    orsx
    obtain ⟨loaded, loadStep, run⟩ := ObservedReach.rs_next run hT
    have loadRun := erase loadStep
    have storage := fun k => Devm.getStorVal_of_state (of_run_sload_state loadRun)
      sevm.currentTarget k
    simp only [St.getStorVal] at storage
    obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
    simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
      List.cons.injEq] at pop push
    obtain ⟨rfl, rfl⟩ := pop
    rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal, storage] at run
    have balanceBound : balance.toNat ≤
        (loaded.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat := by
      rw [← storage]
      exact bounded
    rw [show Bytes.toB256 [11] = (11 : B256) from rfl] at run
    iterate 4 orsx
    first
    | obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
      change some ImplV2.t_4123_c78 = some g at hg
      cases hg
      obtain ⟨D, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
        (show SstoreFreeSet ImplV2.cert.prog [5, 78, 88, 93] = true from by decide +kernel)
        (by decide +kernel) run hT
      obtain ⟨supplySafe, _, _, rfl⟩ :=
        OldBurnNonIncCallees.sub_ret (version := .v2) (by decide) (callee.mono erase)
      unfold ImplV2.t_239f_c45 at run
    | obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
      change some ImplV2_1.t_3d4c_c76 = some g at hg
      cases hg
      obtain ⟨D, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
        (show SstoreFreeSet ImplV2_1.cert.prog [6, 76, 86, 91] = true from by decide +kernel)
        (by decide +kernel) run hT
      obtain ⟨supplySafe, _, _, rfl⟩ :=
        OldBurnNonIncCallees.sub_ret (version := .v2_1) (by decide) (callee.mono erase)
      unfold ImplV2_1.t_2315_c47 at run
    all_goals
      orsd
      orsx
      rw [show Bytes.toB256 [11] = (11 : B256) from rfl] at run
      rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
      · refine ⟨_, _, _, rfl, ?_, .inl rfl⟩
        simp only [St.getStorVal]
        rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat supplySafe)]
        exact Nat.sub_le _ _
      have effect := sstore_getStor_set (xs := []) (erase step) ⟨_, rfl⟩
      obtain ⟨afterStore, G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
      change afterStore.getStor sevm.currentTarget = (loaded.getStor sevm.currentTarget).set
        11 (loaded.getStorVal sevm.currentTarget 11 - amount) at effect
      iterate 4 orsx
      first
      | obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
        change some ImplV2.t_4123_c78 = some g at hg
        cases hg
        obtain ⟨D, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
          (show SstoreFreeSet ImplV2.cert.prog [5, 78, 88, 93] = true from by decide +kernel)
          (by decide +kernel) run hT
        obtain ⟨balanceSafe, _, _, rfl⟩ :=
          OldBurnNonIncCallees.sub_ret (version := .v2) (by decide) (callee.mono erase)
      | obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
        change some ImplV2_1.t_3d4c_c76 = some g at hg
        cases hg
        obtain ⟨D, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
          (show SstoreFreeSet ImplV2_1.cert.prog [6, 76, 86, 91] = true from by decide +kernel)
          (by decide +kernel) run hT
        obtain ⟨balanceSafe, _, _, rfl⟩ :=
          OldBurnNonIncCallees.sub_ret (version := .v2_1) (by decide) (callee.mono erase)
      all_goals
        have remainingBound : (balance - amount).toNat ≤
            (afterStore.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat := by
          change (balance - amount).toNat ≤
            ((afterStore.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 9)).toNat
          rw [effect, Stor.get_set_ite]
          by_cases sameKey : (11 : B256) = mapSlot sevm.caller.toB256 9
          · rw [ite_eq_left sameKey, B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat balanceSafe),
              B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat supplySafe)]
            apply Nat.sub_le_sub_right
            simpa only [← sameKey] using balanceBound
          · rw [ite_eq_right sameKey, B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat balanceSafe)]
            exact (Nat.sub_le _ _).trans balanceBound
        first
        | exact tail_source (version := .v2) (by decide) erase run remainingBound hT cont
        | exact tail_source (version := .v2_1) (by decide) erase run remainingBound hT cont


/-- Original nonincrease API, projected from the stronger observed source. -/
theorem stores_nonInc {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {balance saved amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q version.cert.prog sevm
      ⟨St b (balance :: saved :: amount :: S) M G, supplyStart version, K⟩ T)
    (bounded : balance.toNat ≤
      (b.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := stores_source old erase (ObservedReach.of_reach run) bounded hT cont
  exact ⟨key, value, rest, stack, bound⟩

def body : ModernVersion → SFunc
  | .v2 => ImplV2.t_2178_c45
  | .v2_1 => ImplV2_1.t_20ee_c47
  | .v2_2 => .ret

/-- Original role checks and the actual caller-balance read discharge the store bound. -/
theorem body_source {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (amount :: S) M G, body version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    simp only [body] at run
    first | unfold ImplV2.t_2178_c45 at run | unfold ImplV2_1.t_20ee_c47 at run
    orsd
    orsx
    orsld
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first | unfold ImplV2.t_2202_c45 at run | unfold ImplV2_1.t_2178_c47 at run
    orsd
    iterate 11 orsx
    orsld
    iterate 3 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first | unfold ImplV2.t_226a_c45 at run | unfold ImplV2_1.t_21e0_c47 at run
    orsd
    iterate 11 orsx
    orsld
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first | unfold ImplV2.t_22d3_c45 at run | unfold ImplV2_1.t_2249_c47 at run
    orsd
    iterate 11 orsx
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl,
      show (Bytes.toB256 [64]).toNat = 64 from rfl] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    obtain ⟨loaded, loadStep, run⟩ := ObservedReach.rs_next run hT
    have loadRun := erase loadStep
    have storage := fun k => Devm.getStorVal_of_state (of_run_sload_state loadRun)
      sevm.currentTarget k
    simp only [St.getStorVal] at storage
    obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
    simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
      List.cons.injEq] at pop push
    obtain ⟨rfl, rfl⟩ := pop
    rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal, storage] at run
    iterate 2 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first | unfold ImplV2.t_2339_c45 at run | unfold ImplV2_1.t_22af_c47 at run
    orsd
    iterate 5 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | exact stores_source (version := .v2) (by decide) erase run (Nat.le_refl _) hT cont
    | exact stores_source (version := .v2_1) (by decide) erase run (Nat.le_refl _) hT cont

/-- Original nonincrease API, projected from the stronger observed source. -/
theorem body_nonInc {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q version.cert.prog sevm
      ⟨St b (amount :: S) M G, body version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := body_source old erase (ObservedReach.of_reach run) hT cont
  exact ⟨key, value, rest, stack, bound⟩

end Blanc.Lift.Usdc.OldBurnNonIncBodies
