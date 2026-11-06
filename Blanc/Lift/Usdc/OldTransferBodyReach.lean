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

/-- The owner alternative also retains the bound at that exact store; the recipient alternative
retains that the stored value does not fall. -/
def BoundedObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (owner recipient : Adr) (T : Conf) : Prop :=
  ((∃ value rest, T.d.stack = mapSlot owner.toB256 9 :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget (mapSlot owner.toB256 9)).toNat) ∧
    (∃ tail, T.f = ownerLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (owner.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) ∨
  (((∃ rest, T.d.stack = mapSlot recipient.toB256 9 :: rest) ∧
    (∃ tail, T.f = recipientLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (recipient.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) ∧
    ∀ value rest, T.d.stack = mapSlot recipient.toB256 9 :: value :: rest →
      (T.d.getStorVal sevm.currentTarget (mapSlot recipient.toB256 9)).toNat ≤ value.toNat)

theorem BoundedObservedSource.forget {Q : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {owner recipient : Adr} {T : Conf}
    (source : BoundedObservedSource Q observe sevm owner recipient T) :
    ObservedSource Q observe sevm owner recipient T := by
  rcases source with ⟨⟨value, rest, stack, _⟩, shape, hash⟩ | ⟨recipientSource, _⟩
  · exact .inl ⟨⟨value :: rest, stack⟩, shape, hash⟩
  · exact .inr recipientSource

/-- A 64-byte read at `0` after a word write at `0`, over a memory whose second word reads `right`:
solc's mapping hash reusing the base left at offset `32`. No well-formedness: the write takes its first
branch whenever the backing array reaches past the first word. -/
theorem read_after_left_write (μ : Mem) (left right : B256) (big : 32 ≤ μ.data.size)
    (sized : 32 ≤ μ.size)
    (h : ∀ i < 32, μ.data.getD (32 + i) 0 = right.toBytes.getD i 0) :
    ((μ.write 0 left.toBytes).read 0 64).1 = left.toBytes ++ right.toBytes := by
  obtain ⟨head, tail, shape⟩ : ∃ head tail, left.toBytes = head :: tail := by
    cases hl : left.toBytes with
    | nil =>
      have := B256.length_toBytes left
      simp only [hl, List.length_nil, OfNat.zero_ne_ofNat] at this
    | cons head tail => exact ⟨_, _, rfl⟩
  have len : (head :: tail).length = 32 := by rw [← shape]; exact B256.length_toBytes left
  have data : (μ.write 0 left.toBytes).data = Array.writeD μ.data 0 left.toBytes := by
    rw [shape]
    simp only [Mem.write]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  simp only [Mem.read, Array.sliceD_eq_map]
  apply List.ext_get
  · simp only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range, List.length_append,
      B256.length_toBytes, Nat.reduceAdd]
  · intro i hleft hright
    simp only [List.length_map, List.length_range] at hleft
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, Nat.zero_add]
    have whole : (left.toBytes ++ right.toBytes).getD i 0 = (left.toBytes ++ right.toBytes)[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hright]
      rfl
    refine Eq.trans ?_ whole
    rw [data, Array.getD_writeD (0 : UInt8) _ _ _ _
      (by simp only [B256.length_toBytes]; omega)]
    simp only [B256.length_toBytes, Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero]
    by_cases half : i < 32
    · rw [ite_eq_left half, List.getD_append_left (d := (0 : UInt8))
        (by simpa only [B256.length_toBytes] using half)]
    · rw [ite_eq_right half, List.getD_append_right (d := (0 : UInt8))
        (by simp only [B256.length_toBytes]; omega), B256.length_toBytes,
        ← h (i - 32) (by omega)]
      congr 1
      omega

/-- `keccak_rehash` without well-formedness: the second hash rewrites only the key word of a scratch
image left by the first. -/
theorem keccak_rehash_raw (μ : Mem) (k1 b k2 : B256) :
    ((((((μ.write 0 k1.toBytes).write 32 b.toBytes).read 0 64).2.write
        (Bytes.toB256 [0]).toNat k2.toBytes).read (Bytes.toB256 [0]).toNat
          (Bytes.toB256 [64]).toNat).1).keccak = mapSlot k2 b := by
  unfold mapSlot
  apply congrArg
  rw [show (Bytes.toB256 [0]).toNat = 0 by decide, show (Bytes.toB256 [64]).toNat = 64 by decide]
  have ne : b.toBytes ≠ [] := by
    intro e
    have := B256.length_toBytes b
    simp only [e, List.length_nil, OfNat.zero_ne_ofNat] at this
  have dataSize := Mem.write_end_le_data_size (μ.write 0 k1.toBytes) 32 ne
  rw [B256.length_toBytes] at dataSize
  apply read_after_left_write
  · exact (by omega : 32 ≤ 32 + 32).trans dataSize
  · change 32 ≤ memExtSize ((μ.write 0 k1.toBytes).write 32 b.toBytes).size 0 64
    refine le_trans ?_ (memExtSize_ge _ _ _)
    rw [Mem.size_write_eq, ite_eq_right ne, B256.length_toBytes]
    split_ifs with room
    · omega
    · decide
  · intro i hi
    change ((μ.write 0 k1.toBytes).write 32 b.toBytes).data.getD (32 + i) 0 = _
    rw [Mem.getD_write_below_end _ 32 ne (by simp only [B256.length_toBytes]; omega),
      ite_eq_left (by omega), Nat.add_sub_cancel_left]

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

/-- The recipient writer's store, retaining its own original successful balance hash; the store's value
does not fall from the balance `value` was built on. -/
theorem recipient_reach_core {program : List SFunc} {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {value amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe program sevm
      ⟨St b (value :: amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_40ba_c74, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ((∃ rest, T.d.stack = mapSlot recipient.toB256 9 :: rest) ∧
      (∃ tail, T.f = recipientLine.foldr SFunc.next tail) ∧
      ObservedKeccak Q observe sevm (recipient.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) ∧
    ((b.getStorVal sevm.currentTarget (mapSlot recipient.toB256 9)).toNat ≤ value.toNat →
      ∀ value' rest, T.d.stack = mapSlot recipient.toB256 9 :: value' :: rest →
        (T.d.getStorVal sevm.currentTarget (mapSlot recipient.toB256 9)).toNat ≤ value'.toNat) := by
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
  · refine ⟨⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩, fun credit value' rest stack => ?_⟩
    have same := List.cons.inj (List.cons.inj stack).2
    rw [← same.1]
    simpa only [St.getStorVal] using credit
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The recipient writer retains its own original successful balance hash. -/
theorem recipient_reach_bounded {program : List SFunc} {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {value amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe program sevm
      ⟨St b (value :: amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_40ba_c74, K⟩ T)
    (credit : (b.getStorVal sevm.currentTarget (mapSlot recipient.toB256 9)).toNat ≤ value.toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BoundedObservedSource Q observe sevm owner recipient T :=
  have core := recipient_reach_core erase run hT cont
  .inr ⟨core.1, core.2 credit⟩

/-- The recipient writer's source, whatever `value` holds. -/
theorem recipient_reach_source {program : List SFunc} {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {value amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe program sevm
      ⟨St b (value :: amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_40ba_c74, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T :=
  .inr (recipient_reach_core erase run hT cont).1

def addEntry : ModernVersion → SFunc
  | .v2 => ImplV2.t_41fd_c77
  | .v2_1 => ImplV2_1.t_3e26_c75
  | .v2_2 => .ret

/-- The checked addition returns the unwrapped sum over the same base and memory. -/
theorem add_ret {version : ModernVersion} (old : version ≠ .v2_2)
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256} {M : Mem} {G : Nat} {D : Devm}
    (run : SFunc.Run version.cert.prog sevm
      (St b (x :: y :: tag :: S) M G) (addEntry version) (.returned D)) :
    (x + y).toNat = x.toNat + y.toNat ∧ ∃ G', D = St b ((x + y) :: S) M G' := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    have h := run.cut
    simp only [addEntry] at h
    first | unfold ImplV2.t_41fd_c77 at h | unfold ImplV2_1.t_3e26_c75 at h
    obtain ⟨_, h⟩ := ric_dest h
    iterate 9
      obtain ⟨_, step, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
    ibranch h safe
    first | unfold ImplV2.t_4165_c77 at h | unfold ImplV2_1.t_3d8e_c75 at h
    obtain ⟨_, h⟩ := ric_dest h
    iterate 5
      obtain ⟨_, step, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
    obtain ⟨_, same⟩ := ric_ret h
    exact ⟨(add_nof_of_ltCheck (eq_zero_of_iszero_ne_zero safe)).2, _,
      Outcome.returned.inj (Seg.done.inj same)⟩

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
    obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
    have loadRun := erase loadStep
    obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
    simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
      List.cons.injEq] at pop push
    obtain ⟨rfl, rfl⟩ := pop
    rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal,
      B256.and_comm recipient.toB256 ff20, ff20_and_adr, keccak_rehash_raw,
      show Bytes.toB256 [9] = (9 : B256) from rfl] at run
    have storage := Devm.getStorVal_of_state (of_run_sload_state loadRun)
      sevm.currentTarget (mapSlot recipient.toB256 9)
    simp only [St.getStorVal] at storage
    iterate 4 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | rw [show ImplV2.cert.prog[77]? = some ImplV2.t_41fd_c77 from rfl] at hg
      cases hg
      obtain ⟨returned, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
        (show SstoreFreeSet ImplV2.cert.prog [] = true from by decide +kernel)
        (show ImplV2.t_41fd_c77.sstoreFreeIn [] = true from by decide +kernel) run hT
      obtain ⟨sum, _, rfl⟩ := add_ret (version := .v2) (by decide) (SFunc.RunP.mono erase callee)
      apply recipient_reach_bounded erase run ?_ hT cont
      rw [sum, ← storage]
      exact Nat.le_add_left _ _
    | rw [show ImplV2_1.cert.prog[75]? = some ImplV2_1.t_3e26_c75 from rfl] at hg
      cases hg
      obtain ⟨returned, callee, _, run⟩ := ObservedReach.return_of_sstoreFree
        (show SstoreFreeSet ImplV2_1.cert.prog [] = true from by decide +kernel)
        (show ImplV2_1.t_3e26_c75.sstoreFreeIn [] = true from by decide +kernel) run hT
      obtain ⟨sum, _, rfl⟩ := add_ret (version := .v2_1) (by decide) (SFunc.RunP.mono erase callee)
      rw [recipient_v21] at run
      apply recipient_reach_bounded erase run ?_ hT cont
      rw [sum, ← storage]
      exact Nat.le_add_left _ _

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
