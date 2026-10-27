import Blanc.Lift.Usdc.V2MintReach

/-! Actual V2 transfer stores and their original successful balance hashes. -/
namespace Blanc.Lift.Usdc.V2TransferReach
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

/-- The recipient writer retains its own original successful balance hash. -/
theorem recipient_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {value amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_40ba_c74, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
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
theorem owner_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {value amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_407e_c74, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2.t_407e_c74 at run
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
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 6 orsx
  orsld
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[77]? = some ImplV2.t_41fd_c77 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, run⟩ := V2MintReach.add_reach_observed erase run hT
  exact recipient_reach_observed erase run hT cont

/-- The checked subtraction returns into the first balance writer. -/
theorem debit_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_404e_c74, K⟩ T)
    (enough : B256.eqCheck (B256.gtCheck amount (b.getStorVal sevm.currentTarget
      (mapSlot owner.toB256 9))) 0 ≠ 0)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2.t_404e_c74 at run
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
  rw [show ImplV2.cert.prog[78]? = some ImplV2.t_4123_c78 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V2MintReach.sub_reach_observed erase enough run hT
  exact owner_reach_observed erase run hT cont

/-- The internal transfer body is entered with its actual three arguments. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_3ef8_c74, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2.t_3ef8_c74 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_3f64_c74 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_3fd0_c74 at run
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
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨enough, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  have current := of_run_sload_state loadRun
  have storage : loadedPost.getStorVal sevm.currentTarget (mapSlot owner.toB256 9) =
      b.getStorVal sevm.currentTarget (mapSlot owner.toB256 9) := by
    unfold Devm.getStorVal Devm.getAcct
    rw [← current]
    rfl
  apply debit_reach_observed erase run ?_ hT cont
  rw [storage]
  exact enough

/-- The checked dispatcher routes transfer through its original ABI wrapper. -/
theorem route_transfer : SFunc.selWalk 0xa9059cbb
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb], 116) := by
  decide +kernel

/-- Follow the selected prefix to its store; the final frame outcome is unrestricted. -/
theorem transfer_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm sevm.caller (Sevm.dataWord sevm 4).toAdr T := by
  unfold ImplV2.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0xa9059cbb := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_transfer run hT
  rw [show ImplV2.cert.prog[116]? = some ImplV2.t_09c9_c116 from rfl] at hg
  cases hg
  unfold ImplV2.t_09c9_c116 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_09df_c116 at run
  orsd
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20] at run
  rw [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[28]? = some ImplV2.t_2bb8_c28 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_0407_c116], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2.t_2bb8_c28 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_2c45_c28 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_2cae_c28 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_2d2f_c28 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[74]? = some ImplV2.t_3ef8_c74 from rfl] at hg
  cases hg
  apply body_reach_observed erase run hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  exact cont f member

/-- Actual byte scans identify each reached balance-store tail. -/
theorem ownerPattern_occurrences :
    BytePattern.occurrences (ownerLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x40a9] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem recipientPattern_occurrences :
    BytePattern.occurrences (recipientLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x40e8] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

def ActualSource (root node : Exec.Deriv) (owner recipient : Adr) (key : B256) : Prop :=
  (node.pc = 0x40a9 ∧ key = mapSlot owner.toB256 9 ∧
    ∃ hashPc, KeccakBefore root node (owner.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
  (node.pc = 0x40e8 ∧ key = mapSlot recipient.toB256 9 ∧
    ∃ hashPc, KeccakBefore root node (recipient.toB256.toBytes ++ (9 : B256).toBytes) hashPc)

/-- Every selected successful raw store has its own actual key and earlier hash. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xa9059cbb)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node root.sevm.caller (Sevm.dataWord root.sevm 4).toAdr write.key := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
    ImplV2.cert.prog root.sevm ⟨root.devm, ImplV2.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases transfer_reach_observed (fun h => StepIn.toRun h) selected walk target with
    ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩ | ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩
  · have location := ok.pc_eq_of_prefix_singleton ownerLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide) ownerPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · have location := ok.pc_eq_of_prefix_singleton recipientLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide) recipientPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩

end Blanc.Lift.Usdc.V2TransferReach
