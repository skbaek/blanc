import Blanc.Lift.Usdc.V22TransferFromEntry
import Blanc.Lift.Usdc.OldTransferFromAllowance

/-! The actual V2.2 allowance reload and debit after the balance transfer. -/
namespace Blanc.Lift.Usdc.V22TransferFromAllowance
open Jaune Blanc Blanc.Lift OldTransferFromEntry
variable {observe : Conf → Conf → Prop}

/-- The complete final allowance suffix agrees with the shared older writer. -/
theorem tail_eq : Impl.t_16b3_c68 = ImplV2.t_14b8_c59 := by
  rfl

/-- The actual post-balance reload and checked subtraction bound this exact store,
including when an allowance key aliases a balance key. -/
theorem allowance_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (guardedStack sevm owner recipient amount S) M G, Impl.t_1678_c68, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    OldTransferFromAllowance.StoreSource Q observe Impl.cert.prog sevm owner T := by
  unfold guardedStack Impl.t_1678_c68 at run
  orsd
  iterate 3 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
  iterate 21 orsx
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl,
    show (Bytes.toB256 [64]).toNat = 64 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw, Mem.read_two_word_writes_at_raw] at run
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
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[100]? = some Impl.t_4163_c100 from rfl] at hg
  cases hg
  obtain ⟨bound, _, _, run⟩ := V22TransferFromCallee.subtraction_return erase run hT
  rw [tail_eq] at run
  apply OldTransferFromAllowance.tail_source erase run ?_ hT cont
  rw [B256.toNat_sub_eq_of_le _ _ bound]
  exact Nat.sub_le _ _

/-- Original nonincrease interface, projected from the ordered source. -/
theorem allowance_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (guardedStack sevm owner recipient amount S) M G, Impl.t_1678_c68, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨value, rest, stack, bound, _⟩ := allowance_source erase run hT cont
  exact ⟨_, value, rest, stack, bound⟩

end Blanc.Lift.Usdc.V22TransferFromAllowance
