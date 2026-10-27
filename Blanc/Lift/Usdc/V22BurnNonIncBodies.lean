import Blanc.Lift.Usdc.ModernBurnStores
import Blanc.Lift.Usdc.RefineAdminCallees
import Blanc.Lift.FrameWalkKit

/-! V2_2 burn decreases its actual cells even if the supply and balance keys coincide. -/
namespace Blanc.Lift.Usdc.V22BurnNonIncBodies

open Jaune Blanc Blanc.Lift

/-- A bounded value remains bounded at the final balance writer's own pre-state. -/
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
  unfold Impl.t_4508_c99 at run
  rsd
  iterate 4 rsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 10 rsx
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl,
    show (Bytes.toB256 [64]).toNat = 64 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  rcases Reach.sstoreS run with rfl | ⟨d', step, run⟩
  · exact ⟨_, _, _, rfl, bounded⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel) cont).elim

/-- The cap and blacklist query do not change the cell used by the bounded writer. -/
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
  unfold Impl.t_4430_c99 at run
  rsd
  iterate 5 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel) cont).elim
  unfold Impl.t_44a9_c99 at run
  rsd
  iterate 3 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  change some Impl.t_3f6a_c83 = some g at hg
  cases hg
  unfold Impl.t_3f6a_c83 at run
  rsd
  iterate 12 rsx
  obtain ⟨loaded, loadStep, run⟩ := rs_next run hT
  have loadRun := erase loadStep
  have storage := fun k => Devm.getStorVal_of_state (of_run_sload_state loadRun)
    sevm.currentTarget k
  simp only [St.getStorVal] at storage
  obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at pop push
  obtain ⟨rfl, rfl⟩ := pop
  rw [St.self push (SolcStorageReturn.sload_memory loadRun)] at run
  iterate 5 rsx
  obtain ⟨f, K', G', same, run⟩ := rs_retBase run hT
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  unfold Impl.t_44b2_c99 at run
  rsd
  iterate 2 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel) cont).elim
  apply tail_nonInc erase run ?_ hT cont
  rw [← storage]
  exact bounded

/-- The supply subtraction and the later balance subtraction are bounded even when their keys
coincide. Only the balance read's bound on its pre-state word is needed. -/
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
  unfold Impl.t_24a7_c54 at run
  rsd
  rsx
  obtain ⟨loaded, loadStep, run⟩ := rs_next run hT
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
  iterate 4 rsx
  obtain ⟨_, D, callee, run⟩ := rs_callOver (E := [100]) (by decide +kernel)
    (show Impl.cert.prog[100]? = some Impl.t_4163_c100 from rfl) (by decide) run hT
  obtain ⟨_, rfl, supplySafe⟩ := Impl.sub_ret (callee.mono erase)
  have amountSupply : amount ≤ loaded.getStorVal sevm.currentTarget 11 :=
    B256.not_lt.mp (gtCheck_eq_zero supplySafe)
  unfold Impl.t_24b4_c54 at run
  rsd
  rsx
  rw [show Bytes.toB256 [11] = (11 : B256) from rfl] at run
  rcases Reach.sstoreS run with rfl | ⟨d', step, run⟩
  · refine ⟨_, _, _, rfl, ?_⟩
    simp only [St.getStorVal]
    rw [B256.toNat_sub_eq_of_le _ _ amountSupply]
    exact Nat.sub_le _ _
  have effect := sstore_getStor_set (xs := []) (erase step) ⟨_, rfl⟩
  obtain ⟨afterStore, G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  change afterStore.getStor sevm.currentTarget = (loaded.getStor sevm.currentTarget).set
    11 (loaded.getStorVal sevm.currentTarget 11 - amount) at effect
  iterate 6 rsx
  obtain ⟨_, D, callee, run⟩ := rs_callOver (E := [100]) (by decide +kernel)
    (show Impl.cert.prog[100]? = some Impl.t_4163_c100 from rfl) (by decide) run hT
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
  rsd
  rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  change some Impl.t_4430_c99 = some g at hg
  cases hg
  apply setBalance_nonInc erase run remainingBound hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  · exact cont f member


/-- The actual packed balance read supplies the bound used after the supply store. -/
theorem read_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {saved amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q Impl.cert.prog sevm
      ⟨St b (saved :: amount :: S) M G, Impl.t_23e8_c54, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  unfold Impl.t_23e8_c54 at run
  rsd
  iterate 4 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  change some Impl.t_41da_c96 = some g at hg
  cases hg
  unfold Impl.t_41da_c96 at run
  rsd
  iterate 2 rsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr] at run
  iterate 10 rsx
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl,
    show (Bytes.toB256 [64]).toNat = 64 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  obtain ⟨loaded, loadStep, run⟩ := rs_next run hT
  have loadRun := erase loadStep
  have storage := fun k => Devm.getStorVal_of_state (of_run_sload_state loadRun)
    sevm.currentTarget k
  simp only [St.getStorVal] at storage
  obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at pop push
  obtain ⟨rfl, rfl⟩ := pop
  rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal, storage] at run
  iterate 3 rsx
  obtain ⟨f, K', G', same, run⟩ := rs_retBase run hT
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  unfold Impl.t_23f3_c54 at run
  rsd
  iterate 6 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel) cont).elim
  unfold Impl.t_244e_c54 at run
  rsd
  iterate 5 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel) cont).elim
  apply stores_nonInc erase run ?_ hT cont
  rw [B256.toNat_and]
  exact Nat.and_le_right


end Blanc.Lift.Usdc.V22BurnNonIncBodies
