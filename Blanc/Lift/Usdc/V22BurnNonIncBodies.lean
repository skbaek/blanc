import Blanc.Lift.ObservedReachSplit
import Blanc.Lift.Usdc.ModernBurnStores
import Blanc.Lift.Usdc.RefineAdminCallees
import Blanc.Lift.FrameWalkKit

/-! V2_2 burn decreases its actual cells even if the supply and balance keys coincide. -/
namespace Blanc.Lift.Usdc.V22BurnNonIncBodies

open Jaune Blanc Blanc.Lift

/-- A bounded value remains bounded at the final balance writer's own pre-state. -/
theorem tail_source {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: a.toB256 :: S) M G, Impl.t_4508_c99, K⟩ T)
    (bounded : value.toNat ≤ (b.getStorVal sevm.currentTarget (mapSlot a.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  obtain ⟨⟨rest, stack⟩, unchanged, hash⟩ := ModernBurnStores.packed_tail_store_source erase run hT cont
  refine ⟨_, _, rest, stack, ?_, .inr ⟨a, rfl, hash⟩⟩
  rw [unchanged]
  exact bounded

/-- Original nonincrease API, projected from the stronger observed source. -/
theorem tail_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q Impl.cert.prog sevm
      ⟨St b (value :: a.toB256 :: S) M G, Impl.t_4508_c99, K⟩ T)
    (bounded : value.toNat ≤ (b.getStorVal sevm.currentTarget (mapSlot a.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := tail_source erase (ObservedReach.of_reach run) bounded hT cont
  exact ⟨key, value, rest, stack, bound⟩

/-- The cap and blacklist query do not change the cell used by the bounded writer. -/
theorem setBalance_source {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: a.toB256 :: S) M G, Impl.t_4430_c99, K⟩ T)
    (bounded : value.toNat ≤ (b.getStorVal sevm.currentTarget (mapSlot a.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  obtain ⟨⟨rest, stack⟩, unchanged, hash⟩ := ModernBurnStores.packed_setBalance_store_source erase run hT cont
  refine ⟨_, _, rest, stack, ?_, .inr ⟨a, rfl, hash⟩⟩
  rw [unchanged]
  exact bounded

/-- Original nonincrease API, projected from the stronger observed source. -/
theorem setBalance_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q Impl.cert.prog sevm
      ⟨St b (value :: a.toB256 :: S) M G, Impl.t_4430_c99, K⟩ T)
    (bounded : value.toNat ≤ (b.getStorVal sevm.currentTarget (mapSlot a.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := setBalance_source erase (ObservedReach.of_reach run) bounded hT cont
  exact ⟨key, value, rest, stack, bound⟩

/-- The supply subtraction and the later balance subtraction are bounded even when their keys
coincide. Only the balance read's bound on its pre-state word is needed. -/
theorem stores_source {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {balance saved amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (balance :: saved :: amount :: S) M G, Impl.t_24a7_c54, K⟩ T)
    (bounded : balance.toNat ≤
      (b.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  unfold Impl.t_24a7_c54 at run
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
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_4163_c100 = some g at hg
  cases hg
  obtain ⟨D, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
    (show SstoreFreeSet Impl.cert.prog [100] = true from by decide +kernel)
    (by decide +kernel) run hT
  obtain ⟨_, rfl, supplySafe⟩ := Impl.sub_ret (callee.mono erase)
  have amountSupply : amount ≤ loaded.getStorVal sevm.currentTarget 11 :=
    B256.not_lt.mp (gtCheck_eq_zero supplySafe)
  unfold Impl.t_24b4_c54 at run
  orsd
  orsx
  rw [show Bytes.toB256 [11] = (11 : B256) from rfl] at run
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · refine ⟨_, _, _, rfl, ?_, .inl rfl⟩
    simp only [St.getStorVal]
    rw [B256.toNat_sub_eq_of_le _ _ amountSupply]
    exact Nat.sub_le _ _
  have effect := sstore_getStor_set (xs := []) (erase step) ⟨_, rfl⟩
  obtain ⟨afterStore, G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  change afterStore.getStor sevm.currentTarget = (loaded.getStor sevm.currentTarget).set
    11 (loaded.getStorVal sevm.currentTarget 11 - amount) at effect
  iterate 6 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_4163_c100 = some g at hg
  cases hg
  obtain ⟨D, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
    (show SstoreFreeSet Impl.cert.prog [100] = true from by decide +kernel)
    (by decide +kernel) run hT
  obtain ⟨_, rfl, balanceSafe⟩ := Impl.sub_ret (callee.mono erase)
  have amountBalance : amount ≤ balance :=
    B256.not_lt.mp (gtCheck_eq_zero balanceSafe)
  have remainingBound : (balance - amount).toNat ≤
      (afterStore.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat := by
    change (balance - amount).toNat ≤
      ((afterStore.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 9)).toNat
    rw [effect, Stor.get_set_ite]
    by_cases sameKey : (11 : B256) = mapSlot sevm.caller.toB256 9
    · rw [ite_eq_left sameKey, B256.toNat_sub_eq_of_le _ _ amountBalance,
        B256.toNat_sub_eq_of_le _ _ amountSupply]
      apply Nat.sub_le_sub_right
      simpa only [← sameKey] using balanceBound
    · rw [ite_eq_right sameKey, B256.toNat_sub_eq_of_le _ _ amountBalance]
      exact (Nat.sub_le _ _).trans balanceBound
  unfold Impl.t_21cf_c54 at run
  orsd
  orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_4430_c99 = some g at hg
  cases hg
  apply setBalance_source erase run remainingBound hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  · exact cont f member


/-- Original nonincrease API, projected from the stronger observed source. -/
theorem stores_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {balance saved amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q Impl.cert.prog sevm
      ⟨St b (balance :: saved :: amount :: S) M G, Impl.t_24a7_c54, K⟩ T)
    (bounded : balance.toNat ≤
      (b.getStorVal sevm.currentTarget (mapSlot sevm.caller.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := stores_source erase (ObservedReach.of_reach run) bounded hT cont
  exact ⟨key, value, rest, stack, bound⟩

/-- The actual packed balance read supplies the bound used after the supply store. -/
theorem read_source {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {saved amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (saved :: amount :: S) M G, Impl.t_23e8_c54, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  unfold Impl.t_23e8_c54 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_41da_c96 = some g at hg
  cases hg
  unfold Impl.t_41da_c96 at run
  orsd
  iterate 2 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr] at run
  iterate 10 orsx
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
  iterate 3 orsx
  obtain ⟨f, K', G', same, run⟩ := ObservedReach.rs_retBase run hT
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  unfold Impl.t_23f3_c54 at run
  orsd
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_244e_c54 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  apply stores_source erase run ?_ hT cont
  rw [B256.toNat_and]
  exact Nat.and_le_right


/-- Original nonincrease API, projected from the stronger observed source. -/
theorem read_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {saved amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q Impl.cert.prog sevm
      ⟨St b (saved :: amount :: S) M G, Impl.t_23e8_c54, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := read_source erase (ObservedReach.of_reach run) hT cont
  exact ⟨key, value, rest, stack, bound⟩

end Blanc.Lift.Usdc.V22BurnNonIncBodies
