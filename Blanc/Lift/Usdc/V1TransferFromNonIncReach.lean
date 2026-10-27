import Blanc.Lift.Usdc.V1MintReach

/-! V1 transferFrom's allowance reload and checked-subtraction suffix. -/
namespace Blanc.Lift.Usdc.V1TransferFromNonIncReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

/-- The V1 checked subtraction retains the current base and proves its nonwrapping bound. -/
theorem sub_reach_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (x :: y :: tag :: S) M G, ImplV1.t_2e12_c44, f :: K⟩ T)
    (hT : AtSstore T) :
    x ≤ y ∧ ∃ G', ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b ((y - x) :: S) M G', f, K⟩ T := by
  unfold ImplV1.t_2e12_c44 at run
  orsd
  iterate 8 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨safe, _, run⟩
  · unfold ImplV1.t_2e1f_c44 at run
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, step, _⟩
    · obtain ⟨_, impossible⟩ := hT
      cases impossible
    · cases step.1
  have bound : x ≤ y := by
    apply B256.not_lt.mp
    intro bad
    apply safe
    rw [show B256.gtCheck x y = 1 from ite_eq_left bad]
    decide +kernel
  refine ⟨bound, ?_⟩
  unfold ImplV1.t_2e20_c44 at run
  orsd
  iterate 9 orsx
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨next, ⟨step, _⟩, suffix⟩
  · obtain ⟨_, impossible⟩ := hT
    cases impossible
  · cases step with
    | ret t pop =>
      obtain ⟨_, same⟩ := St.of_pop1 pop
      exact ⟨_, same ▸ suffix⟩


/-- The value at the reached store is bounded by that same configuration's current cell. -/
def AllowanceNonIncAt (sevm : Sevm) (owner : Adr) (T : Conf) : Prop :=
  ∃ value rest, T.d.stack = mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10) :: value :: rest ∧
    value.toNat ≤ (T.d.getStorVal sevm.currentTarget
      (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10))).toNat

/-- The two balance source tails remain alternatives to the allowance bound. -/
def BalanceOrNonInc (sevm : Sevm) (owner : Adr) (T : Conf) : Prop :=
  (∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop)
    (.next (.push [0x13, 0x91] (by decide)) tail))) ∨
  (∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop)
    (.next (.push [0x14, 0x63] (by decide)) tail))) ∨ AllowanceNonIncAt sevm owner T

/-- Recomputing both allowance hashes changes no storage before the final write. -/
theorem allowance_reach_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {value a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_1463_c13, K⟩ T)
    (bound : value.toNat ≤ (b.getStorVal sevm.currentTarget
      (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10))).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AllowanceNonIncAt sevm owner T := by
  unfold ImplV1.t_1463_c13 at run
  orsd
  iterate 7 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, _, run⟩ := ObservedKeccak.of_next erase run hT
    (input := owner.toB256.toBytes ++ (10 : B256).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 6 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, _, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.caller.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · refine ⟨value, value :: a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S, ?_, ?_⟩
    · simp only [St.stack, mapSlot, show (Bytes.toB256 [10]) = (10 : B256) from rfl]
    · simpa only [St.getStorVal] using bound
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The recipient write can stop before the later allowance hashes. -/
theorem recipient_reach_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {value a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_1391_c13, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BalanceOrNonInc sevm owner T := by
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
  · exact .inr (.inl ⟨_, rfl⟩)
  obtain ⟨b', G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, _, run⟩ := ObservedKeccak.of_next erase run hT
    (input := owner.toB256.toBytes ++ (10 : B256).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 6 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, _, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.caller.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  rw [show (Bytes.toB256 [10]) = (10 : B256) from rfl] at run
  obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
  have loadRun := erase loadStep
  obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at pop push
  obtain ⟨rfl, rfl⟩ := pop
  have current := of_run_sload_state loadRun
  have storage : loadedPost.getStorVal sevm.currentTarget
      (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10)) =
      b'.getStorVal sevm.currentTarget
        (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10)) := by
    unfold Devm.getStorVal Devm.getAcct
    rw [← current]
    rfl
  simp only [mapSlot] at storage
  rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal, ← storage] at run
  simp only [St.memory] at run
  iterate 6 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[44]? = some ImplV1.t_2e12_c44 from rfl] at hg
  cases hg
  obtain ⟨safe, G3, run⟩ := sub_reach_nonInc erase run hT
  apply Or.inr ∘ Or.inr
  apply allowance_reach_nonInc erase run ?_ hT cont
  rw [B256.toNat_sub_eq_of_le _ _ safe]
  exact Nat.sub_le _ _

/-- The owner write can stop before either later mapping write. -/
theorem owner_reach_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {value a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_12fc_c13, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BalanceOrNonInc sevm owner T := by
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
  · exact .inl ⟨_, rfl⟩
  obtain ⟨b', G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 21 orsx
  orsld
  iterate 6 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[45]? = some ImplV1.t_2e2b_c45 from rfl] at hg
  cases hg
  obtain ⟨b'', G3, run⟩ := V1MintReach.add_reach_observed erase run hT
  exact recipient_reach_nonInc erase run hT cont

/-- The actual subtraction helper returns into the first balance writer. -/
theorem body_reach_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm}
    {a c d e amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (a :: c :: d :: e :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV1.t_12aa_c13, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    BalanceOrNonInc sevm owner T := by
  unfold ImplV1.t_12aa_c13 at run
  orsd
  iterate 20 orsx
  orsld
  iterate 6 orsx
  obtain ⟨g, G1, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[44]? = some ImplV1.t_2e12_c44 from rfl] at hg
  cases hg
  obtain ⟨b', G2, run⟩ := V1BurnReach.sub_reach_observed erase run hT
  exact owner_reach_nonInc erase run hT cont


end Blanc.Lift.Usdc.V1TransferFromNonIncReach
