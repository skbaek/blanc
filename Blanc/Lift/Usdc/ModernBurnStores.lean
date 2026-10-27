import Blanc.Lift.Usdc.ModernCallerReach

/-! Original balance-store keys and hashes used by the modern burn routes. -/
namespace Blanc.Lift.Usdc.ModernBurnStores

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

def callerTail : ModernVersion → SFunc
  | .v2 => ImplV2.t_23ac_c45
  | .v2_1 => ImplV2_1.t_2322_c47
  | .v2_2 => Impl.t_4508_c99

/-- The two older burn tails hash the caller and base 9 immediately before their store.
The packed V2_2 layout uses the separate address-preserving helper below. -/
theorem caller_key_hash {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: S) M G, callerTail version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    (∃ rest, T.d.stack = mapSlot sevm.caller.toB256 9 :: rest) ∧
      ObservedKeccak Q observe sevm
        (sevm.caller.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    simp only [callerTail] at run
    first
    | unfold ImplV2.t_23ac_c45 at run
    | unfold ImplV2_1.t_2322_c47 at run
    orsd
    iterate 14 orsx
    obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
      (input := sevm.caller.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    iterate 3 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · exact ⟨⟨_, rfl⟩, hash⟩
    exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- V2_2's final balance writer hashes its masked address, with the same original edge witness. -/
theorem packed_tail_key_hash {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: a.toB256 :: S) M G, Impl.t_4508_c99, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    (∃ rest, T.d.stack = mapSlot a.toB256 9 :: rest) ∧
      ObservedKeccak Q observe sevm (a.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
  unfold Impl.t_4508_c99 at run
  orsd
  iterate 4 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 9 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact ⟨⟨_, rfl⟩, hash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The actual cap and blacklist checks preserve the account through their internal return.
No successful final frame or supplied storage separation is required. -/
theorem packed_setBalance_key_hash {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: a.toB256 :: S) M G, Impl.t_4430_c99, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    (∃ rest, T.d.stack = mapSlot a.toB256 9 :: rest) ∧
      ObservedKeccak Q observe sevm (a.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
  unfold Impl.t_4430_c99 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_44a9_c99 at run
  orsd
  iterate 3 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_3f6a_c83 = some g at hg
  cases hg
  unfold Impl.t_3f6a_c83 at run
  orsd
  iterate 12 orsx
  orsld
  iterate 5 orsx
  obtain ⟨f, K', b', G', same, run⟩ := ObservedReach.rs_retM run hT
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  unfold Impl.t_44b2_c99 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact packed_tail_key_hash erase run hT cont

end Blanc.Lift.Usdc.ModernBurnStores
