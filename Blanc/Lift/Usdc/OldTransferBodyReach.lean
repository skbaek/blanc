import Blanc.Lift.Usdc.V2_1MintReach
import Blanc.Lift.ObservedReachSplit
import Blanc.Lift.Usdc.OldBurnNonIncCallees

/-! Shared V2/V2.1 transfer-body walks with original hashes and same-node debit bounds. -/
namespace Blanc.Lift.Usdc.OldTransferBodyReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

def ownerLine : List Ninst := [.reg .sstore, .reg (.swap 0), .reg (.dup 4)]
def recipientLine : List Ninst := [.reg .sstore, .reg (.dup 0), .reg .mload, .reg (.dup 5)]

def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (owner recipient : Adr) (T : Conf) : Prop :=
  ((∃ rest, T.d.stack = mapSlot owner.toB256 9 :: rest) ∧
    (∃ tail, T.f = ownerLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (owner.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) ∨
  ((∃ rest, T.d.stack = mapSlot recipient.toB256 9 :: rest) ∧
    (∃ tail, T.f = recipientLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (recipient.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True))

/-- The owner alternative also retains the bound at that exact store. -/
def BoundedObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (owner recipient : Adr) (T : Conf) : Prop :=
  ((∃ value rest, T.d.stack = mapSlot owner.toB256 9 :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget (mapSlot owner.toB256 9)).toNat) ∧
    (∃ tail, T.f = ownerLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (owner.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) ∨
  ((∃ rest, T.d.stack = mapSlot recipient.toB256 9 :: rest) ∧
    (∃ tail, T.f = recipientLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (recipient.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True))

theorem BoundedObservedSource.forget {Q : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {owner recipient : Adr} {T : Conf}
    (source : BoundedObservedSource Q observe sevm owner recipient T) :
    ObservedSource Q observe sevm owner recipient T := by
  rcases source with ⟨⟨value, rest, stack, _⟩, shape, hash⟩ | recipientSource
  · exact .inl ⟨⟨value :: rest, stack⟩, shape, hash⟩
  · exact .inr recipientSource

def ownerStart : ModernVersion → SFunc
  | .v2 => ImplV2.t_407e_c74
  | .v2_1 => ImplV2_1.t_3ca7_c73
  | .v2_2 => .ret

def debitStart : ModernVersion → SFunc
  | .v2 => ImplV2.t_404e_c74
  | .v2_1 => ImplV2_1.t_3c77_c73
  | .v2_2 => .ret

def body : ModernVersion → SFunc
  | .v2 => ImplV2.t_3ef8_c74
  | .v2_1 => ImplV2_1.t_3b21_c73
  | .v2_2 => .ret

/-- The complete recipient suffix is identical across the two runtimes. -/
theorem recipient_v21 : ImplV2_1.t_3ce3_c73 = ImplV2.t_40ba_c74 := by
  rfl

/-- The recipient writer retains its own original successful balance hash. -/
theorem recipient_reach_bounded {program : List SFunc} {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {value amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe program sevm
      ⟨St b (value :: amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_40ba_c74, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BoundedObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2.t_40ba_c74 at run
  orsd
  iterate 4 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm recipient.toB256 ff20, ff20_and_adr] at run
  iterate 13 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := recipient.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 3 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The first balance writer observes only its own hash before the store. -/
theorem owner_reach_bounded {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {value amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: amount :: recipient.toB256 :: owner.toB256 :: S) M G, ownerStart version, K⟩ T)
    (bounded : value.toNat ≤
      (b.getStorVal sevm.currentTarget (mapSlot owner.toB256 9)).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BoundedObservedSource Q observe sevm owner recipient T := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    simp only [ownerStart, ModernVersion.cert] at run
    first | unfold ImplV2.t_407e_c74 at run | unfold ImplV2_1.t_3ca7_c73 at run
    orsd
    iterate 4 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
    iterate 10 orsx
    obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
      (input := owner.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    iterate 3 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · exact .inl ⟨⟨_, _, rfl, bounded⟩, ⟨_, rfl⟩, hash⟩
    obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
    iterate 6 orsx
    orsld
    iterate 4 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | rw [show ImplV2.cert.prog[77]? = some ImplV2.t_41fd_c77 from rfl] at hg
      cases hg
      obtain ⟨_, _, _, run⟩ := V2MintReach.add_reach_observed erase run hT
      exact recipient_reach_bounded erase run hT cont
    | rw [show ImplV2_1.cert.prog[75]? = some ImplV2_1.t_3e26_c75 from rfl] at hg
      cases hg
      obtain ⟨_, _, _, run⟩ := V2_1MintReach.add_reach_observed erase run hT
      rw [recipient_v21] at run
      exact recipient_reach_bounded erase run hT cont

/-- The checked subtraction returns into the first balance writer. -/
theorem debit_reach_bounded {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, debitStart version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BoundedObservedSource Q observe sevm owner recipient T := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    simp only [debitStart, ModernVersion.cert] at run
    first | unfold ImplV2.t_404e_c74 at run | unfold ImplV2_1.t_3c77_c73 at run
    orsd
    iterate 3 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
    iterate 9 orsx
    obtain ⟨_, _, run⟩ := ObservedKeccak.of_next erase run hT
      (input := owner.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
    have loadRun := erase loadStep
    obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
    simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
      List.cons.injEq] at pop push
    obtain ⟨rfl, rfl⟩ := pop
    rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal] at run
    iterate 4 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | rw [show ImplV2.cert.prog[78]? = some ImplV2.t_4123_c78 from rfl] at hg
      cases hg
      obtain ⟨returned, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
        (show SstoreFreeSet ImplV2.cert.prog [5, 78, 88, 93] = true from by decide +kernel)
        (show ImplV2.t_4123_c78.sstoreFreeIn [5, 78, 88, 93] = true from by decide +kernel) run hT
      obtain ⟨bound, _, _, rfl⟩ := OldBurnNonIncCallees.sub_ret
        (version := .v2) (by decide) (SFunc.RunP.mono erase callee)
      apply owner_reach_bounded (version := .v2) (by decide) erase run ?_ hT cont
    | rw [show ImplV2_1.cert.prog[76]? = some ImplV2_1.t_3d4c_c76 from rfl] at hg
      cases hg
      obtain ⟨returned, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
        (show SstoreFreeSet ImplV2_1.cert.prog [6, 76, 86, 91] = true from by decide +kernel)
        (show ImplV2_1.t_3d4c_c76.sstoreFreeIn [6, 76, 86, 91] = true from by decide +kernel) run hT
      obtain ⟨bound, _, _, rfl⟩ := OldBurnNonIncCallees.sub_ret
        (version := .v2_1) (by decide) (SFunc.RunP.mono erase callee)
      apply owner_reach_bounded (version := .v2_1) (by decide) erase run ?_ hT cont
    all_goals
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat bound)]
      have storage := Devm.getStorVal_of_state (of_run_sload_state loadRun)
        sevm.currentTarget (mapSlot owner.toB256 9)
      simp only [St.getStorVal] at storage
      rw [← storage]
      exact Nat.sub_le _ _

/-- The internal transfer body is entered with its actual three arguments. -/
theorem body_reach_bounded {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, body version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BoundedObservedSource Q observe sevm owner recipient T := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    simp only [body, ModernVersion.cert] at run
    first | unfold ImplV2.t_3ef8_c74 at run | unfold ImplV2_1.t_3b21_c73 at run
    orsd
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first | unfold ImplV2.t_3f64_c74 at run | unfold ImplV2_1.t_3b8d_c73 at run
    orsd
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first | unfold ImplV2.t_3fd0_c74 at run | unfold ImplV2_1.t_3bf9_c73 at run
    orsd
    iterate 3 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
    iterate 9 orsx
    obtain ⟨_, _, run⟩ := ObservedKeccak.of_next erase run hT
      (input := owner.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
    have loadRun := erase loadStep
    obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
    simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
      List.cons.injEq] at pop push
    obtain ⟨rfl, rfl⟩ := pop
    rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal] at run
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | exact debit_reach_bounded (version := .v2) (by decide) erase run hT cont
    | exact debit_reach_bounded (version := .v2_1) (by decide) erase run hT cont

end Blanc.Lift.Usdc.OldTransferBodyReach
