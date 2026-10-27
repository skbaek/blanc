import Blanc.Lift.Usdc.V2ConfigureMinterReach
import Blanc.Lift.Usdc.ImplV2_1.Check

/-! V2.1 configureMinter actual-store keys and hashes, reusing the identical V2 body. -/
namespace Blanc.Lift.Usdc.V2_1ConfigureMinterReach

open Jaune Blanc Blanc.Lift
open V2ConfigureMinterReach (ObservedSource flagLine allowanceLine)

variable {observe : Conf → Conf → Prop}

/-- The checked dispatcher routes configureMinter through its original ABI wrapper. -/
theorem route_configure : SFunc.selWalk 0x4e44d956
    (.next (.reg (.dup 0)) (.next (.push [0x7f, 0x2e, 0xec, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xb2] (by decide))
        (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))) =
    .inl (Bytes.toB256 [0x4e, 0x44, 0xd9, 0x56], 126) := by
  decide +kernel

/-- Follow the selected prefix to its store; the final frame outcome is unrestricted. -/
theorem configure_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x4e44d956)
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b S M G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T := by
  unfold ImplV2_1.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0x4e44d956 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_configure run hT
  rw [show ImplV2_1.cert.prog[126]? = some ImplV2_1.t_081a_c126 from rfl] at hg
  cases hg
  unfold ImplV2_1.t_081a_c126 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_0830_c126 at run
  orsd
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20] at run
  rw [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[41]? = some ImplV2_1.t_23a8_c41 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2_1.t_03f1_c126], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2_1.t_23a8_c41 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_2435_c41 at run
  orsd
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact V2ConfigureMinterReach.body_reach_observed erase run hT cont

/-- Exact scans over the registered V2.1 runtime identify the two source tails. -/
theorem flagPattern_occurrences :
    BytePattern.occurrences (flagLine.flatMap Ninst.toBytes) ImplV2_1.code.toList = [0x24f6] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem allowancePattern_occurrences :
    BytePattern.occurrences (allowanceLine.flatMap Ninst.toBytes) ImplV2_1.code.toList = [0x2501] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- Locate the flag store from its own final checked cursor. -/
theorem flagStore_pc {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV2_1.code ImplV2_1.cert node κ) {tail : SFunc}
    (tree : κ.f = flagLine.foldr SFunc.next tail) : node.pc = 0x24f6 := by
  exact ok.pc_eq_of_prefix_singleton flagLine tail tree
    (suffix := []) (by simp only [List.append_nil]) (by decide) flagPattern_occurrences

/-- Locate the allowance store independently of any assumed key equality. -/
theorem allowanceStore_pc {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV2_1.code ImplV2_1.cert node κ) {tail : SFunc}
    (tree : κ.f = allowanceLine.foldr SFunc.next tail) : node.pc = 0x2501 := by
  exact ok.pc_eq_of_prefix_singleton allowanceLine tail tree
    (suffix := []) (by simp only [List.append_nil]) (by decide) allowancePattern_occurrences

/-- The actual source alternative carries its own successful original hash before the store. -/
def ActualSource (root node : Exec.Deriv) (a : Adr) (key : B256) : Prop :=
  (node.pc = 0x24f6 ∧ key = mapSlot a.toB256 12 ∧
    ∃ hashPc, KeccakBefore root node (a.toB256.toBytes ++ (12 : B256).toBytes) hashPc) ∨
  (node.pc = 0x2501 ∧ key = mapSlot a.toB256 13 ∧
    ∃ hashPc, KeccakBefore root node (a.toB256.toBytes ++ (13 : B256).toBytes) hashPc)

/-- All selected successful raw stores are covered, whatever the final frame outcome. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x4e44d956)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr write.key := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2_1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2_1.code ImplV2_1.cert root node)
    ImplV2_1.cert.prog root.sevm ⟨root.devm, ImplV2_1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
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

end Blanc.Lift.Usdc.V2_1ConfigureMinterReach
