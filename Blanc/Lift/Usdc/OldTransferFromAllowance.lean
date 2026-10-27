import Blanc.Lift.Usdc.OldTransferFromEntry
import Blanc.Lift.CursorKeccakOrder

/-! The original post-transfer allowance reload and debit in V2/V2.1. -/
namespace Blanc.Lift.Usdc.OldTransferFromAllowance
open Jaune Blanc Blanc.Lift OldTransferFromEntry
variable {observe : Conf → Conf → Prop}

/-- The complete final allowance suffix is identical across old versions. -/
theorem tail_v21 : ImplV2_1.t_13b0_c58 = ImplV2.t_14b8_c59 := by
  rfl

/-- The common instruction prefix at the final transferFrom allowance store. -/
def storeLine : List Ninst := [.reg .sstore, .push [1] (by decide), .reg (.swap 3), .reg .pop]

/-- The final transferFrom allowance store and its two ordered successful hashes. -/
def StoreSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (program : List SFunc)
    (sevm : Sevm) (owner : Adr) (T : Conf) : Prop :=
  ∃ value rest,
    T.d.stack = mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10) :: value :: rest ∧
    value.toNat ≤ (T.d.getStorVal sevm.currentTarget
      (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10))).toNat ∧
    (∃ tail, T.f = storeLine.foldr SFunc.next tail) ∧
    ObservedKeccakPair Q observe program sevm
      (owner.toB256.toBytes ++ (10 : B256).toBytes)
      (sevm.caller.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)

/-- The final allowance tail writes the value bounded against this exact storage base. -/
theorem tail_source {program : List SFunc} {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount value : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe program sevm
      ⟨St b (value :: guardedStack sevm owner recipient amount S) M G,
        ImplV2.t_14b8_c59, K⟩ T)
    (bounded : value.toNat ≤ (b.getStorVal sevm.currentTarget
      (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10))).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    StoreSource Q observe program sevm owner T := by
  unfold ImplV2.t_14b8_c59 guardedStack at run
  orsd
  iterate 3 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
  iterate 12 orsx
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
    (input := owner.toB256.toBytes ++ (10 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run firstHash
  rw [Mem.read_two_word_writes_at_raw] at run firstHash
  have run := run.withPrefix
  iterate 7 orsx
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.caller.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact ⟨_, _, rfl, bounded, ⟨_, rfl⟩, _, firstHash, secondHash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- Original nonincrease interface, projected from the ordered source. -/
theorem tail_nonInc {program : List SFunc} {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount value : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe program sevm
      ⟨St b (value :: guardedStack sevm owner recipient amount S) M G,
        ImplV2.t_14b8_c59, K⟩ T)
    (bounded : value.toNat ≤ (b.getStorVal sevm.currentTarget
      (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10))).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨value, rest, stack, bound, _⟩ := tail_source erase run bounded hT cont
  exact ⟨_, value, rest, stack, bound⟩

/-- Reload after the balance transfer, then use the actual checked subtraction return.
Even an allowance/balance hash alias cannot invalidate this same-node bound. -/
theorem allowance_source {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (guardedStack sevm owner recipient amount S) M G,
        OldTransferFromEntry.returnTail version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    StoreSource Q observe version.cert.prog sevm owner T := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    simp only [ModernVersion.cert, OldTransferFromEntry.returnTail] at run
    unfold guardedStack at run
    first | unfold ImplV2.t_147d_c59 at run | unfold ImplV2_1.t_1375_c58 at run
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
    first
    | rw [show ImplV2.cert.prog[78]? = some ImplV2.t_4123_c78 from rfl] at hg
      cases hg
      obtain ⟨bound, _, _, _, run⟩ := OldTransferFromCallee.subtraction_return
        (version := .v2) (by decide) erase run hT
    | rw [show ImplV2_1.cert.prog[76]? = some ImplV2_1.t_3d4c_c76 from rfl] at hg
      cases hg
      obtain ⟨bound, _, _, _, run⟩ := OldTransferFromCallee.subtraction_return
        (version := .v2_1) (by decide) erase run hT
      rw [tail_v21] at run
    all_goals
      apply tail_source erase run ?_ hT cont
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat bound)]
      exact Nat.sub_le _ _

/-- Original nonincrease interface, projected from the ordered source. -/
theorem allowance_nonInc {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (guardedStack sevm owner recipient amount S) M G,
        OldTransferFromEntry.returnTail version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨value, rest, stack, bound, _⟩ := allowance_source old erase run hT cont
  exact ⟨_, value, rest, stack, bound⟩

end Blanc.Lift.Usdc.OldTransferFromAllowance
