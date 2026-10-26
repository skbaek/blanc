import Blanc.Lift.Usdc.V1MintReach

/-! Actual V1 transfer balance stores and their mapping-key hash occurrences. -/
namespace Blanc.Lift.Usdc.V1TransferReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

def recipientStoreLead : List Ninst :=
  [.reg .sstore, .reg .pop, .reg (.dup 4),
    .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
    .reg .and, .reg .caller,
    .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
    .reg .and,
    .push [0xdd,0xf2,0x52,0xad,0x1b,0xe2,0xc8,0x9b,0x69,0xc2,0xb0,0x68,0xfc,0x37,0x8d,0xaa,
      0x95,0x2b,0xa7,0xf1,0x63,0xc4,0xa1,0x16,0x28,0xf5,0x5a,0x4d,0xf5,0x23,0xb3,0xef] (by decide)]

def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (recipient : Adr) (T : Conf) : Prop :=
  ((∃ rest, T.d.stack = mapSlot sevm.caller.toB256 9 :: rest) ∧
    (∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.push [0x26, 0xfa] (by decide)) tail))) ∧
    ObservedKeccak Q observe sevm (sevm.caller.toB256.toBytes ++ (9 : B256).toBytes)
      (fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
        (.next (.reg .sstore) (.next (.reg .pop)
          (.next (.push [0x26, 0xfa] (by decide)) tail))))) ∨
  ((∃ rest, T.d.stack = mapSlot recipient.toB256 9 :: rest) ∧
    (∃ tail, T.f = recipientStoreLead.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (recipient.toB256.toBytes ++ (9 : B256).toBytes)
      (fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
        (recipientStoreLead.foldr SFunc.next tail)))

/-- The last transfer write consumes the recipient balance hash. -/
theorem recipient_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {value a c d amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: amount :: recipient.toB256 :: S) M G, ImplV1.t_26fa_c31, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  unfold ImplV1.t_26fa_c31 at run
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
      (recipientStoreLead.foldr SFunc.next tail))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by exact ⟨_, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The caller balance write precedes the recipient addition and write. -/
theorem caller_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {value a c d amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: a :: c :: d :: amount :: recipient.toB256 :: S) M G,
        ImplV1.t_2665_c31, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  unfold ImplV1.t_2665_c31 at run
  orsd
  iterate 7 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.caller.toB256.toBytes ++ (9 : B256).toBytes)
    (shape := fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
      (.next (.reg .sstore) (.next (.reg .pop) (.next (.push [0x26, 0xfa] (by decide)) tail))))
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

/-- The body subtracts the caller balance before its first write. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {a c d amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (a :: c :: d :: amount :: recipient.toB256 :: S) M G,
        ImplV1.t_2613_c31, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  unfold ImplV1.t_2613_c31 at run
  orsd
  iterate 20 orsx
  orsld
  iterate 6 orsx
  obtain ⟨g, G1, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[44]? = some ImplV1.t_2e12_c44 from rfl] at hg
  cases hg
  obtain ⟨b', G2, run⟩ := V1BurnReach.sub_reach_observed erase run hT
  exact caller_reach_observed erase run hT cont

/-- V1's checked dispatcher selects the transfer wrapper. -/
theorem route_transfer : SFunc.selWalk 0xa9059cbb
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb], 74) := by
  decide +kernel

/-- Follow the selected transfer prefix through the concrete runtime guards. -/
theorem transfer_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ObservedSource Q observe sevm (Blanc.Sevm.dataWord sevm 4).toAdr T := by
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
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase route_transfer run hT
  rw [show ImplV1.cert.prog[74]? = some ImplV1.t_0960_c74 from rfl] at hg
  cases hg
  unfold ImplV1.t_0960_c74 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_096c_c74 at run
  orsd
  iterate 34 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[31]? = some ImplV1.t_24ab_c31 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_09ab_c74], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_24ab_c31 at run
  orsd
  iterate 4 orsx
  orsld
  iterate 11 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_24c9_c31 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_2529_c31 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_2589_c31 at run
  orsd
  iterate 11 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_25c5_c31 at run
  orsd
  iterate 18 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_observed erase run hT cont

/-- Whole-code byte checks locate the concrete transfer write tails. -/
theorem caller_pattern_occurrences :
    Blanc.BytePattern.occurrences [0x55, 0x50, 0x61, 0x26, 0xfa] ImplV1.code.toList = [0x26a7] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem recipient_pattern_occurrences :
    Blanc.BytePattern.occurrences (recipientStoreLead.flatMap Ninst.toBytes)
      ImplV1.code.toList = [0x273c] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- Every actual transfer write is a caller or recipient balance row, with its own
successful hash on the same original prefix. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xa9059cbb)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x26a7 ∧ write.key = mapSlot root.sevm.caller.toB256 9 ∧
      KeccakBefore root node (root.sevm.caller.toB256.toBytes ++ (9 : B256).toBytes) 0x26a4) ∨
    (node.pc = 0x273c ∧ write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      KeccakBefore root node ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes)
        0x2739) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases transfer_reach_observed (fun h => StepIn.toRun h) selected walk target with
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩ | ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩
  · have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
    have location : node.pc = 0x26a7 := ok.pc_eq_of_prefix_singleton
      [.reg .sstore, .reg .pop, .push [0x26, 0xfa] (by decide)] tail source
      (suffix := []) (by decide +kernel) (by decide +kernel) caller_pattern_occurrences
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
      [.reg .sstore, .reg .pop, .push [0x26, 0xfa] (by decide)] hashTail hashTree
      (suffix := []) (by decide +kernel) (by decide +kernel) caller_pattern_occurrences
    rw [wordStoreHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x26a4 := by omega
    exact .inl ⟨location, keyEq,
      occurrence, next, hashPc, instruction, result, reached, edge, suffix, hashStack, read⟩
  · have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
    have location : node.pc = 0x273c := ok.pc_eq_of_prefix_singleton
      recipientStoreLead tail source
      (suffix := []) (by decide +kernel) (by decide +kernel) recipient_pattern_occurrences
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
      recipientStoreLead hashTail hashTree
      (suffix := []) (by decide +kernel) (by decide +kernel) recipient_pattern_occurrences
    rw [wordStoreHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x2739 := by omega
    exact .inr ⟨location, keyEq,
      occurrence, next, hashPc, instruction, result, reached, edge, suffix, hashStack, read⟩

end Blanc.Lift.Usdc.V1TransferReach
