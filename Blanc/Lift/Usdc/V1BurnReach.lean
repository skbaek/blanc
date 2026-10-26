import Blanc.BytePattern
import Blanc.Lift.CursorCheckPrefix
import Blanc.Lift.CursorKeccak
import Blanc.Lift.Usdc.ImplV1.Check
import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.WalkCutKit

/-! Actual V1 burn stores: fixed supply slot or caller balance with its earlier hash. -/
namespace Blanc.Lift.Usdc.V1BurnReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (T : Conf) : Prop :=
  ((∃ rest, T.d.stack = 11 :: rest) ∧
    ∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.push [0x1e, 0xe5] (by decide)) tail))) ∨
  ((∃ rest, T.d.stack = mapSlot sevm.caller.toB256 9 :: rest) ∧
    (∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop) (.next (.reg .caller) tail))) ∧
    ObservedKeccak Q observe sevm (sevm.caller.toB256.toBytes ++ (9 : B256).toBytes)
      (fun f => ∃ tail, f = wordStoreHashLead.foldr SFunc.next
        (.next (.reg .sstore) (.next (.reg .pop) (.next (.reg .caller) tail)))))

/-- Complete bytecode checks identify the two burn store tails. -/
theorem supply_pattern_occurrences :
    Blanc.BytePattern.occurrences [0x55, 0x50, 0x61, 0x1e, 0xe5] ImplV1.code.toList = [0x1ed1] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem balance_pattern_occurrences :
    Blanc.BytePattern.occurrences [0x55, 0x50, 0x33] ImplV1.code.toList = [0x1f27] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The final balance writer retains its own actual successful hash. -/
theorem balance_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (value :: S) M G, ImplV1.t_1ee5_c20, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm T := by
  unfold ImplV1.t_1ee5_c20 at run
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
      (.next (.reg .sstore) (.next (.reg .pop) (.next (.reg .caller) tail))))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by exact ⟨_, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The original checked subtraction helper returns through the same observed continuation. -/
theorem sub_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (x :: y :: tag :: S) M G, ImplV1.t_2e12_c44, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' G', ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b' ((y - x) :: S) M G', f, K⟩ T := by
  unfold ImplV1.t_2e12_c44 at run
  orsd
  iterate 8 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · unfold ImplV1.t_2e1f_c44 at run
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, step, _⟩
    · obtain ⟨_, impossible⟩ := hT
      cases impossible
    · cases step.1
  unfold ImplV1.t_2e20_c44 at run
  orsd
  iterate 9 orsx
  obtain ⟨f', K', b', G', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact ⟨b', G', run⟩

/-- The fixed supply store precedes the balance writer, with both internal returns preserved. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x balance amount tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (x :: balance :: amount :: tag :: S) M G, ImplV1.t_1eb7_c20, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm T := by
  unfold ImplV1.t_1eb7_c20 at run
  orsd
  iterate 3 orsx
  orsld
  iterate 6 orsx
  obtain ⟨g, G1, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[44]? = some ImplV1.t_2e12_c44 from rfl] at hg
  cases hg
  obtain ⟨b', G2, run⟩ := sub_reach_observed erase run hT
  unfold ImplV1.t_1ecc_c20 at run
  orsd
  iterate 3 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨b'', G3, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 10 orsx
  obtain ⟨g, G4, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[44]? = some ImplV1.t_2e12_c44 from rfl] at hg
  cases hg
  obtain ⟨nextBase, G5, run⟩ := sub_reach_observed erase run hT
  exact balance_reach_observed erase run hT cont

/-- V1's checked dispatcher selects its original burn wrapper. -/
theorem route_burn : SFunc.selWalk 0x42966c68
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0x42, 0x96, 0x6c, 0x68], 64) := by
  decide +kernel

/-- Follow the actual selected prefix, preserving observations at its reached store. -/
theorem burn_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm T := by
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
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase route_burn run hT
  rw [show ImplV1.cert.prog[64]? = some ImplV1.t_0659_c64 from rfl] at hg
  cases hg
  unfold ImplV1.t_0659_c64 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_0665_c64 at run
  orsd
  iterate 23 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[20]? = some ImplV1.t_1d7a_c20 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_0684_c64], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_1d7a_c20 at run
  orsd
  iterate 4 orsx
  orsld
  iterate 11 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_1d98_c20 at run
  orsd
  iterate 23 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_1df7_c20 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_1e57_c20 at run
  orsd
  iterate 18 orsx
  orsld
  iterate 8 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_1ea8_c20 at run
  orsd
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_observed erase run hT cont

/-- An actual burn store is the fixed supply write or the original caller-balance write. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x1ed1 ∧ write.key = 11) ∨
    (node.pc = 0x1f27 ∧ write.key = mapSlot root.sevm.caller.toB256 9 ∧
      KeccakBefore root node (root.sevm.caller.toB256.toBytes ++ (9 : B256).toBytes) 0x1f24) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases burn_reach_observed (fun h => StepIn.toRun h) selected walk target with
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩⟩ | ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩
  · have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
    have location : node.pc = 0x1ed1 := ok.pc_eq_of_prefix_singleton
      [.reg .sstore, .reg .pop, .push [0x1e, 0xe5] (by decide)] tail source
      (suffix := []) (by decide +kernel) (by decide +kernel) supply_pattern_occurrences
    exact .inl ⟨location, keyEq⟩
  · have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
    have location : node.pc = 0x1f27 := ok.pc_eq_of_prefix_singleton
      [.reg .sstore, .reg .pop, .reg .caller] tail source
      (suffix := []) (by decide +kernel) (by decide +kernel) balance_pattern_occurrences
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
      [.reg .sstore, .reg .pop, .reg .caller] hashTail hashTree
      (suffix := []) (by decide +kernel) (by decide +kernel) balance_pattern_occurrences
    rw [wordStoreHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x1f24 := by omega
    exact .inr ⟨location, keyEq,
      occurrence, next, hashPc, instruction, result, reached, edge, suffix, hashStack, read⟩

end Blanc.Lift.Usdc.V1BurnReach
