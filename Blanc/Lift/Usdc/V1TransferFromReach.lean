import Blanc.Lift.Usdc.V1MintReach
import Blanc.Lift.CursorKeccakOrder

/-! Actual V1 transferFrom stores and their earlier mapping hashes. -/
namespace Blanc.Lift.Usdc.V1TransferFromReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

/-- The allowance store has a distinctive source suffix after its two hashes. -/
def allowanceStoreLead : List Ninst :=
  [.reg .sstore, .reg .pop, .reg (.dup 5),
    .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
    .reg .and, .reg (.dup 7)]

/-- The first allowance hash's literal path through the second hash to its store. -/
def allowanceHashLead : List Ninst :=
  [.reg .keccak256, .push [0x00] (by decide), .reg .caller,
    .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
    .reg .and,
    .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
    .reg .and, .reg (.dup 1), .reg .mstore, .push [0x20] (by decide), .reg .add,
    .reg (.swap 0), .reg (.dup 1), .reg .mstore, .push [0x20] (by decide), .reg .add,
    .push [0x00] (by decide), .reg .keccak256, .reg (.dup 1), .reg (.swap 0)]

/-- At each store only that row's already executed hashes are required. -/
def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (owner recipient : Adr) (T : Conf) : Prop :=
  ((∃ rest, T.d.stack = mapSlot owner.toB256 9 :: rest) ∧
    (∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.push [0x13, 0x91] (by decide)) tail))) ∧
    ObservedKeccak Q observe sevm (owner.toB256.toBytes ++ (9 : B256).toBytes)
      (fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
        (.next (.reg .sstore) (.next (.reg .pop)
          (.next (.push [0x13, 0x91] (by decide)) tail))))) ∨
  ((∃ rest, T.d.stack = mapSlot recipient.toB256 9 :: rest) ∧
    (∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.push [0x14, 0x63] (by decide)) tail))) ∧
    ObservedKeccak Q observe sevm (recipient.toB256.toBytes ++ (9 : B256).toBytes)
      (fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
        (.next (.reg .sstore) (.next (.reg .pop)
          (.next (.push [0x14, 0x63] (by decide)) tail))))) ∨
  ((∃ rest, T.d.stack = mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10) :: rest) ∧
    (∃ tail, T.f = allowanceStoreLead.foldr SFunc.next tail) ∧
    ∃ middle : Conf,
    ObservedKeccak Q (fun before after => observe before after ∧ after = middle)
      sevm (owner.toB256.toBytes ++ (10 : B256).toBytes)
      (fun f => ∃ tail, f = allowanceHashLead.foldr SFunc.next
        (allowanceStoreLead.foldr SFunc.next tail)) ∧
    ObservedKeccak Q (fun before after => observe before after ∧
      ObservedReach Q observe ImplV1.cert.prog sevm middle before) sevm
      (sevm.caller.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
      (fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
        (allowanceStoreLead.foldr SFunc.next tail)))

/-- The final allowance writer computes both levels of the owner/caller mapping. -/
theorem allowance_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {value a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_1463_c13, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV1.t_1463_c13 at run
  orsd
  iterate 7 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
    (input := owner.toB256.toBytes ++ (10 : B256).toBytes)
    (shape := fun f => ∃ tail, f = allowanceHashLead.foldr SFunc.next
      (allowanceStoreLead.foldr SFunc.next tail))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by exact ⟨_, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run firstHash
  rw [Mem.read_two_word_writes_at_raw] at run firstHash
  have run := run.withPrefix
  iterate 6 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.caller.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
    (shape := fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
      (allowanceStoreLead.foldr SFunc.next tail))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by exact ⟨_, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inr (.inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, _, firstHash, secondHash⟩)
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The recipient write can stop before the later allowance hashes. -/
theorem recipient_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {value a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_1391_c13, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV1.t_1391_c13 at run
  orsd
  iterate 7 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := recipient.toB256.toBytes ++ (9 : B256).toBytes)
    (shape := fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
      (.next (.reg .sstore) (.next (.reg .pop) (.next (.push [0x14, 0x63] (by decide)) tail))))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by exact ⟨_, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inr (.inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩)
  obtain ⟨b', G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 38 orsx
  orsld
  iterate 6 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[44]? = some ImplV1.t_2e12_c44 from rfl] at hg
  cases hg
  obtain ⟨b'', G3, run⟩ := V1BurnReach.sub_reach_observed erase run hT
  exact allowance_reach_observed erase run hT cont

/-- The owner write can stop before either later mapping write. -/
theorem owner_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {value a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_12fc_c13, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV1.t_12fc_c13 at run
  orsd
  iterate 7 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := owner.toB256.toBytes ++ (9 : B256).toBytes)
    (shape := fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
      (.next (.reg .sstore) (.next (.reg .pop) (.next (.push [0x13, 0x91] (by decide)) tail))))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by exact ⟨_, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  obtain ⟨b', G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 21 orsx
  orsld
  iterate 6 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[45]? = some ImplV1.t_2e2b_c45 from rfl] at hg
  cases hg
  obtain ⟨b'', G3, run⟩ := V1MintReach.add_reach_observed erase run hT
  exact recipient_reach_observed erase run hT cont

/-- The actual subtraction helper returns into the first balance writer. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_12aa_c13, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV1.t_12aa_c13 at run
  orsd
  iterate 20 orsx
  orsld
  iterate 6 orsx
  obtain ⟨g, G1, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[44]? = some ImplV1.t_2e12_c44 from rfl] at hg
  cases hg
  obtain ⟨b', G2, run⟩ := V1BurnReach.sub_reach_observed erase run hT
  exact owner_reach_observed erase run hT cont

/-- V1's checked dispatcher selects the transferFrom wrapper. -/
theorem route_transferFrom : SFunc.selWalk 0x23b872dd
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd], 57) := by
  decide +kernel

/-- The selected actual prefix reaches the transferFrom body with its original continuation. -/
theorem transferFrom_body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ (base : Devm) (a c d e amount : B256) (rest : List B256) (mem : Mem)
      (gas : Nat) (saved : List SFunc),
      ObservedReach Q observe ImplV1.cert.prog sevm
        ⟨St base (a :: c :: d :: e :: amount :: (Sevm.dataWord sevm 36).toAdr.toB256 ::
          (Sevm.dataWord sevm 4).toAdr.toB256 :: rest) mem gas, ImplV1.t_12aa_c13, saved⟩ T ∧
      (∀ f ∈ saved, f.sstoreFreeIn [] = true) := by
  unfold ImplV1.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_000d_c0 at run
  iterate 7 orsx
  have word := (dispatchWord_eq_selector sevm).trans selected
  unfold Proxy.dispatchWord at word
  rw [word] at run
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase route_transferFrom run hT
  rw [show ImplV1.cert.prog[57]? = some ImplV1.t_02f3_c57 from rfl] at hg
  cases hg
  unfold ImplV1.t_02f3_c57 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_02ff_c57 at run
  orsd
  iterate 14 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  iterate 11 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  iterate 20 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[13]? = some ImplV1.t_1057_c13 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_035e_c57], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_1057_c13 at run
  orsd
  iterate 4 orsx
  orsld
  iterate 11 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_1075_c13 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_10d5_c13 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_1135_c13 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_1195_c13 at run
  orsd
  iterate 11 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_11d1_c13 at run
  orsd
  iterate 18 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_121f_c13 at run
  orsd
  iterate 35 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact ⟨_, _, _, _, _, _, _, _, _, _, run, cont⟩

/-- Follow only the actual selected prefix through its concrete V1 guards. -/
theorem transferFrom_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr T := by
  obtain ⟨base, a, c, d, e, amount, rest, mem, gas, saved, body, cont⟩ :=
    transferFrom_body_reach_observed erase selected run hT
  exact body_reach_observed erase body hT cont

/-- Whole-code byte patterns locate the three literal store tails. -/
theorem owner_pattern_occurrences :
    Blanc.BytePattern.occurrences [0x55, 0x50, 0x61, 0x13, 0x91] ImplV1.code.toList = [0x133e] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem recipient_pattern_occurrences :
    Blanc.BytePattern.occurrences [0x55, 0x50, 0x61, 0x14, 0x63] ImplV1.code.toList = [0x13d3] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem allowance_pattern_occurrences :
    Blanc.BytePattern.occurrences [0x55, 0x50, 0x85, 0x73,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0x16,0x87]
      ImplV1.code.toList = [0x14e2] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem allowanceHashLead_size : (allowanceHashLead.map Ninst.size).sum = 64 := by
  decide +kernel

/-- Every actual successful write retains the original mapping-key hash before its own store. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x133e ∧ write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      KeccakBefore root node ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes)
        0x133b) ∨
    (node.pc = 0x13d3 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∧
      KeccakBefore root node ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes)
        0x13d0) ∨
    (node.pc = 0x14e2 ∧ write.key = mapSlot root.sevm.caller.toB256
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10) ∧
      KeccakBefore root node ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        0x14a2 ∧
      KeccakBefore root node (root.sevm.caller.toB256.toBytes ++
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes) 0x14df ∧
      KeccakPairBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        (root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes)) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases transferFrom_reach_observed (fun h => StepIn.toRun h) selected walk target with
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩ |
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩ |
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩, middle, innerHash, outerHash⟩
  · have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
    have location : node.pc = 0x133e := ok.pc_eq_of_prefix_singleton
      [.reg .sstore, .reg .pop, .push [0x13, 0x91] (by decide)] tail source
      (suffix := []) (by decide +kernel) (by decide +kernel) owner_pattern_occurrences
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
      [.reg .sstore, .reg .pop, .push [0x13, 0x91] (by decide)] hashTail hashTree
      (suffix := []) (by decide +kernel) (by decide +kernel) owner_pattern_occurrences
    rw [wordStoreHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x133b := by omega
    exact .inl ⟨location, keyEq,
      occurrence, next, hashPc, instruction, result, reached, edge, suffix, hashStack, read⟩
  · have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
    have location : node.pc = 0x13d3 := ok.pc_eq_of_prefix_singleton
      [.reg .sstore, .reg .pop, .push [0x14, 0x63] (by decide)] tail source
      (suffix := []) (by decide +kernel) (by decide +kernel) recipient_pattern_occurrences
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
      [.reg .sstore, .reg .pop, .push [0x14, 0x63] (by decide)] hashTail hashTree
      (suffix := []) (by decide +kernel) (by decide +kernel) recipient_pattern_occurrences
    rw [wordStoreHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x13d0 := by omega
    exact .inr (.inl ⟨location, keyEq,
      occurrence, next, hashPc, instruction, result, reached, edge, suffix, hashStack, read⟩)
  · have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
    have location : node.pc = 0x14e2 := ok.pc_eq_of_prefix_singleton
      allowanceStoreLead tail source
      (suffix := []) (by decide +kernel) (by decide +kernel) allowance_pattern_occurrences
    obtain ⟨ib, ia, irun, iobs, itree, istack, iread, ishape⟩ := innerHash
    obtain ⟨ob, oa, orun, oobs, otree, ostack, oread, oshape⟩ := outerHash
    have ordered : ObservedKeccakPair (StepIn root)
        (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node) ImplV1.cert.prog root.sevm
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        (root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes) :=
      ⟨middle, ⟨ib, ia, irun, iobs, itree, istack, iread, trivial⟩,
        ⟨ob, oa, orun, oobs, otree, ostack, oread, trivial⟩⟩
    have innerHash : ObservedKeccak (StepIn root)
        (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node) root.sevm
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        (fun f => ∃ tail, f = allowanceHashLead.foldr SFunc.next
          (allowanceStoreLead.foldr SFunc.next tail)) :=
      ⟨ib, ia, irun, iobs.1, itree, istack, iread, ishape⟩
    have outerHash : ObservedKeccak (StepIn root)
        (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node) root.sevm
        (root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes)
        (fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
          (allowanceStoreLead.foldr SFunc.next tail)) :=
      ⟨ob, oa, orun, oobs.1, otree, ostack, oread, oshape⟩
    refine .inr (.inr ⟨location, keyEq, ?_, ?_, ordered.actual⟩)
    · obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
        placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := innerHash.actual
      have offset := placed.pc_add_eq_of_prefix_singleton allowanceHashLead
        allowanceStoreLead hashTail hashTree
        (suffix := []) (by decide +kernel) (by decide +kernel) allowance_pattern_occurrences
      rw [allowanceHashLead_size] at offset
      have hashPc : occurrence.node.pc = 0x14a2 := by omega
      exact ⟨occurrence, next, hashPc, instruction, result, reached, edge, suffix, hashStack, read⟩
    · obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
        placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := outerHash.actual
      have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
        allowanceStoreLead hashTail hashTree
        (suffix := []) (by decide +kernel) (by decide +kernel) allowance_pattern_occurrences
      rw [wordStoreHashLead_size] at offset
      have hashPc : occurrence.node.pc = 0x14df := by omega
      exact ⟨occurrence, next, hashPc, instruction, result, reached, edge, suffix, hashStack, read⟩

end Blanc.Lift.Usdc.V1TransferFromReach
