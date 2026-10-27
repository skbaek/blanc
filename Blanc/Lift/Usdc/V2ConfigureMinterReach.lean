import Blanc.Lift.CursorKeccak
import Blanc.Lift.CursorCheckPrefix
import Blanc.Lift.Usdc.ImplV2.Check
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.WalkCutKit

/-! Actual V2 configureMinter stores and their original successful hash occurrences. -/
namespace Blanc.Lift.Usdc.V2ConfigureMinterReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

/-- V2's two distinct store tails, used only to identify the reached instruction. -/
def flagLine : List Ninst := [.reg .sstore, .push [0x0d] (by decide), .reg (.dup 2)]

def allowanceLine : List Ninst :=
  [.reg .sstore, .reg (.dup 1), .reg .mload, .reg (.dup 5), .reg (.dup 1),
   .reg .mstore, .reg (.swap 1), .reg .mload,
   .push [0x46,0x98,0x0f,0xca,0x91,0x2e,0xf9,0xbc,0xdb,0xd3,0x68,0x77,0x42,0x7b,0x6b,0x90,
     0xe8,0x60,0x76,0x9f,0x60,0x4e,0x89,0xc0,0xe6,0x77,0x20,0xce,0xce,0x53,0x0d,0x20] (by decide)]

/-- Each alternative retains only the reached store and its own prior hash. -/
def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (a : Adr) (T : Conf) : Prop :=
  ((∃ tail, T.f = flagLine.foldr SFunc.next tail) ∧
    (∃ rest, T.d.stack = mapSlot a.toB256 12 :: rest) ∧
    ObservedKeccak Q observe sevm (a.toB256.toBytes ++ (12 : B256).toBytes) (fun _ => True)) ∨
  ((∃ tail, T.f = allowanceLine.foldr SFunc.next tail) ∧
    (∃ rest, T.d.stack = mapSlot a.toB256 13 :: rest) ∧
    ObservedKeccak Q observe sevm (a.toB256.toBytes ++ (13 : B256).toBytes) (fun _ => True))

/-- Abstract the guard memory and surrounding program before traversing the two writes.
The identical V2.1 body can reuse this proof without copying its instruction walk. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {z amount t : B256} {S : List B256}
    {M : Mem} {G : Nat} {K fs : List SFunc} {T : Conf}
    (run : ObservedReach Q observe fs sevm
      ⟨St b (z :: amount :: a.toB256 :: t :: S) M G, ImplV2.t_2553_c41, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm a T := by
  unfold ImplV2.t_2553_c41 at run
  orsd
  iterate 3 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm, ff20_and_adr] at run
  iterate 12 orsx
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (12 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, firstHash⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 6 orsx
  have read :
      (((((M.write 0 a.toB256.toBytes).write 32 (12 : B256).toBytes).read 0 64).2.write
        32 (13 : B256).toBytes).read 0 64).1 = a.toB256.toBytes ++ (13 : B256).toBytes := by
    rw [← Mem.read_two_word_writes_at_raw M 0 a.toB256 (13 : B256)]
    simp only [Mem.read, Mem.extend, Array.sliceD_eq_map, Nat.zero_add]
    apply List.map_congr_left
    intro i hi
    have bound : i < 64 := List.mem_range.mp hi
    conv_lhs => rw [Mem.getD_write_below_end _ 32 (by decide)
      (by rw [B256.length_toBytes]; omega)]
    conv_rhs => rw [Mem.getD_write_below_end _ 32 (by decide)
      (by rw [B256.length_toBytes]; omega)]
    split_ifs with half
    · rfl
    · change ((M.write 0 a.toB256.toBytes).write 32 (12 : B256).toBytes).data.getD i 0 =
        (M.write 0 a.toB256.toBytes).data.getD i 0
      rw [Mem.getD_write_below_end _ 32 (by decide) (by rw [B256.length_toBytes]; omega),
        ite_eq_right half]
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (13 : B256).toBytes) (shape := fun _ => True)
    read (by trivial)
  simp only [show (Bytes.toB256 [32]).toNat = 32 from rfl,
    show Bytes.toB256 [12] = (12 : B256) from rfl,
    show Bytes.toB256 [13] = (13 : B256) from rfl] at run
  rw [read] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d'', _, _, run⟩
  · exact .inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, secondHash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The checked dispatcher routes configureMinter through its original ABI wrapper. -/
theorem route_configure : SFunc.selWalk 0x4e44d956
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0x4e, 0x44, 0xd9, 0x56], 129) := by
  decide +kernel

/-- Follow the selected prefix to its store; the final frame outcome is unrestricted. -/
theorem configure_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x4e44d956)
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
      0x4e44d956 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_configure run hT
  rw [show ImplV2.cert.prog[129]? = some ImplV2.t_080d_c129 from rfl] at hg
  cases hg
  unfold ImplV2.t_080d_c129 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_0823_c129 at run
  orsd
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20] at run
  rw [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[41]? = some ImplV2.t_2456_c41 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_0407_c129], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2.t_2456_c41 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_24e3_c41 at run
  orsd
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_observed erase run hT cont

/-- Exact scans over the registered V2 runtime identify the two source tails. -/
theorem flagPattern_occurrences :
    BytePattern.occurrences (flagLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x25a4] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem allowancePattern_occurrences :
    BytePattern.occurrences (allowanceLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x25af] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- Locate the flag store from its own final checked cursor. -/
theorem flagStore_pc {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV2.code ImplV2.cert node κ) {tail : SFunc}
    (tree : κ.f = flagLine.foldr SFunc.next tail) : node.pc = 0x25a4 := by
  exact ok.pc_eq_of_prefix_singleton flagLine tail tree
    (suffix := []) (by simp only [List.append_nil]) (by decide) flagPattern_occurrences

/-- Locate the allowance store independently of any assumed key equality. -/
theorem allowanceStore_pc {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV2.code ImplV2.cert node κ) {tail : SFunc}
    (tree : κ.f = allowanceLine.foldr SFunc.next tail) : node.pc = 0x25af := by
  exact ok.pc_eq_of_prefix_singleton allowanceLine tail tree
    (suffix := []) (by simp only [List.append_nil]) (by decide) allowancePattern_occurrences

/-- The actual source alternative carries its own successful original hash before the store. -/
def ActualSource (root node : Exec.Deriv) (a : Adr) (key : B256) : Prop :=
  (node.pc = 0x25a4 ∧ key = mapSlot a.toB256 12 ∧
    ∃ hashPc, KeccakBefore root node (a.toB256.toBytes ++ (12 : B256).toBytes) hashPc) ∨
  (node.pc = 0x25af ∧ key = mapSlot a.toB256 13 ∧
    ∃ hashPc, KeccakBefore root node (a.toB256.toBytes ++ (13 : B256).toBytes) hashPc)

/-- All selected successful raw stores are covered, whatever the final frame outcome. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x4e44d956)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr write.key := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
    ImplV2.cert.prog root.sevm ⟨root.devm, ImplV2.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  have source := configure_reach_observed (fun h => StepIn.toRun h) selected walk target
  rcases source with ⟨⟨tail, shape⟩, ⟨other, keyStack⟩, hash⟩ |
      ⟨⟨tail, shape⟩, ⟨other, keyStack⟩, hash⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨flagStore_pc ok shape, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr ⟨allowanceStore_pc ok shape, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩

end Blanc.Lift.Usdc.V2ConfigureMinterReach
