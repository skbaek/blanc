import Blanc.Lift.Usdc.V2ConfigureMinterReach

/-! Actual V2 mint store classification and original successful mapping hashes. -/
namespace Blanc.Lift.Usdc.V2MintReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

def supplyLine : List Ninst :=
  [.reg .sstore, .push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide), .reg (.dup 6)]

def balanceLine : List Ninst :=
  [.reg .sstore, .push [0x20,0xc0] (by decide), .reg (.dup 1), .reg (.dup 6),
    .push [0x41,0x23] (by decide)]

def minterLine : List Ninst := [.reg .sstore, .reg (.dup 0), .reg .mload, .reg (.dup 8)]

def ObservedSourceFor (balanceLine : List Ninst) (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (recipient : Adr) (T : Conf) : Prop :=
  ((∃ rest, T.d.stack = 11 :: rest) ∧ ∃ tail, T.f = supplyLine.foldr SFunc.next tail) ∨
  ((∃ rest, T.d.stack = mapSlot recipient.toB256 9 :: rest) ∧
    (∃ tail, T.f = balanceLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (recipient.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) ∨
  ((∃ rest, T.d.stack = mapSlot sevm.caller.toB256 13 :: rest) ∧
    (∃ tail, T.f = minterLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (sevm.caller.toB256.toBytes ++ (13 : B256).toBytes) (fun _ => True))

abbrev ObservedSource := ObservedSourceFor balanceLine

/-- The V2 checked addition helper returns to the original observed continuation. -/
theorem add_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (x :: y :: tag :: S) M G, ImplV2.t_41fd_c77, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' value G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (value :: S) M G', f, K⟩ T := by
  unfold ImplV2.t_41fd_c77 at run
  orsd
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · unfold ImplV2.t_420b_c77 at run
    repeat orsx
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, step, _⟩
    · obtain ⟨_, impossible⟩ := hT
      cases impossible
    · cases step.1
  unfold ImplV2.t_4165_c77 at run
  orsd
  iterate 5 orsx
  obtain ⟨f', K', b', G', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact ⟨_, _, _, run⟩

/-- The already traversed mint bound excludes the subtraction error branch. -/
theorem sub_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (enough : B256.eqCheck (B256.gtCheck x y) 0 ≠ 0)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (x :: y :: tag :: S) M G, ImplV2.t_4123_c78, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' value M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (value :: S) M' G', f, K⟩ T := by
  unfold ImplV2.t_4123_c78 at run
  orsd
  iterate 22 orsx
  obtain ⟨g, G', hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[88]? = some ImplV2.t_4be2_c88 from rfl] at hg
  cases hg
  unfold ImplV2.t_4be2_c88 at run
  orsd
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨bad, _, run⟩ | ⟨-, _, run⟩
  · exact (enough bad).elim
  unfold ImplV2.t_4c8b_c88 at run
  orsd
  iterate 6 orsx
  obtain ⟨f', K', b', G'', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  unfold ImplV2.t_4165_c78 at run
  orsd
  iterate 5 orsx
  obtain ⟨f'', K'', b'', lastGas, same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact ⟨_, _, _, _, run⟩

/-- The last mint store retains the caller/base13 hash from its own prefix. -/
theorem minter_store_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K fs : List SFunc} {T : Conf}
    (run : ObservedReach Q observe fs sevm
      ⟨St b (value :: S) M G, ImplV2.t_20c0_c44, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    (∃ rest, T.d.stack = mapSlot sevm.caller.toB256 13 :: rest) ∧
    (∃ tail, T.f = minterLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (sevm.caller.toB256.toBytes ++ (13 : B256).toBytes)
      (fun _ => True) := by
  unfold ImplV2.t_20c0_c44 at run
  orsd
  iterate 14 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.caller.toB256.toBytes ++ (13 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 3 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', _, _, run⟩
  · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The last mint store retains the caller/base13 hash from its own prefix. -/
theorem minter_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: S) M G, ImplV2.t_20c0_c44, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  exact .inr (.inr (minter_store_reach_observed erase run hT cont))

/-- Balance and minter-allowance stores keep their distinct original hash inputs. -/
theorem balance_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {value quota a c d amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (enough : B256.eqCheck (B256.gtCheck amount quota) 0 ≠ 0)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: quota :: a :: c :: d :: amount :: recipient.toB256 :: S) M G,
        ImplV2.t_2090_c44, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  unfold ImplV2.t_2090_c44 at run
  orsd
  iterate 3 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm, ff20_and_adr] at run
  iterate 9 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := recipient.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inr (.inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩)
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[78]? = some ImplV2.t_4123_c78 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := sub_reach_observed erase enough run hT
  exact minter_reach_observed erase run hT cont

/-- Supply is the first write; the two mapping stores follow actual helper returns. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {quota a c d amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (enough : B256.eqCheck (B256.gtCheck amount quota) 0 ≠ 0)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (quota :: a :: c :: d :: amount :: recipient.toB256 :: S) M G,
        ImplV2.t_2050_c44, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  unfold ImplV2.t_2050_c44 at run
  orsd
  orsx
  orsld
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[77]? = some ImplV2.t_41fd_c77 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, run⟩ := add_reach_observed erase run hT
  unfold ImplV2.t_205d_c44 at run
  orsd
  orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 13 orsx
  orsld
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[77]? = some ImplV2.t_41fd_c77 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, run⟩ := add_reach_observed erase run hT
  exact balance_reach_observed erase enough run hT cont

/-- The checked dispatcher selects the original mint ABI wrapper. -/
theorem route_mint : SFunc.selWalk 0x40c10f19
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19], 132) := by
  decide +kernel

/-- Follow every selected mint store through the actual ABI and guard prefix. -/
theorem mint_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T := by
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
      0x40c10f19 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_mint run hT
  rw [show ImplV2.cert.prog[132]? = some ImplV2.t_07af_c132 from rfl] at hg
  cases hg
  unfold ImplV2.t_07af_c132 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_07c5_c132 at run
  orsd
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20] at run
  rw [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[44]? = some ImplV2.t_1d43_c44 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_0407_c132], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2.t_1d43_c44 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1dd0_c44 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 3 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1e38_c44 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1ea1_c44 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1f22_c44 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1f8e_c44 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1fe7_c44 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨enough, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_observed erase enough run hT cont

/-- Exact registered-runtime scans identify the three source tails. -/
theorem supplyPattern_occurrences :
    BytePattern.occurrences (supplyLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x2060] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem balancePattern_occurrences :
    BytePattern.occurrences (balanceLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x20b6] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem minterPattern_occurrences :
    BytePattern.occurrences (minterLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x20d7] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- Every actual selected store is supply, recipient balance, or caller minter allowance.
Each mapping alternative retains its own successful original hash before that store. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x40c10f19)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x2060 ∧ write.key = 11) ∨
    (node.pc = 0x20b6 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.pc = 0x20d7 ∧ write.key = mapSlot root.sevm.caller.toB256 13 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.caller.toB256.toBytes ++ (13 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
    ImplV2.cert.prog root.sevm ⟨root.devm, ImplV2.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases mint_reach_observed (fun h => StepIn.toRun h) selected walk target with
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩⟩ |
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩ | ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩
  · exact .inl ⟨ok.pc_eq_of_prefix_singleton supplyLine tail source
      (suffix := []) (by simp only [List.append_nil]) (by decide) supplyPattern_occurrences,
      (List.cons.inj (stack.symm.trans keyStack)).1⟩
  · have location := ok.pc_eq_of_prefix_singleton balanceLine tail source
      (suffix := []) (by simp only [List.append_nil]) (by decide) balancePattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr (.inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)
  · have location := ok.pc_eq_of_prefix_singleton minterLine tail source
      (suffix := []) (by simp only [List.append_nil]) (by decide) minterPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr (.inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)

end Blanc.Lift.Usdc.V2MintReach
