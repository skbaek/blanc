import Blanc.Lift.Usdc.V22TransferReach
import Blanc.Lift.Usdc.V2MintReach

/-! Original V2.2 mint stores and each mapping write's own successful hash. -/
namespace Blanc.Lift.Usdc.V22MintReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

def supplyLine : List Ninst :=
  [.reg .sstore, .push [0x21, 0xd4] (by decide), .reg (.dup 6)]

abbrev minterLine := V2MintReach.minterLine

def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (recipient : Adr) (T : Conf) : Prop :=
  ((∃ rest, T.d.stack = 11 :: rest) ∧ ∃ tail, T.f = supplyLine.foldr SFunc.next tail) ∨
  V22TransferReach.StoreSource Q observe sevm recipient 0x21d4 T ∨
  ((∃ rest, T.d.stack = mapSlot sevm.caller.toB256 13 :: rest) ∧
    (∃ tail, T.f = minterLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm (sevm.caller.toB256.toBytes ++ (13 : B256).toBytes) (fun _ => True))

/-- The identical final minter store reuses its existing original-hash proof. -/
theorem minter_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: S) M G, Impl.t_21de_c53, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  exact .inr (.inr (V2MintReach.minter_store_reach_observed erase run hT cont))

/-- Supply, packed balance and minter allowance follow the actual helper returns. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {quota a c d amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (quota :: a :: c :: d :: amount :: recipient.toB256 :: S) M G,
        Impl.t_21a8_c53, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm recipient T := by
  unfold Impl.t_21a8_c53 at run
  orsd
  orsx
  orsld
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[98]? = some Impl.t_43b5_c98 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, run⟩ := V22TransferReach.add_reach_observed erase run hT
  unfold Impl.t_21b5_c53 at run
  orsd
  orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 7 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[96]? = some Impl.t_41da_c96 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.balance_reach_observed erase run hT
  unfold Impl.t_21c9_c53 at run
  orsd
  iterate 2 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[98]? = some Impl.t_43b5_c98 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, run⟩ := V22TransferReach.add_reach_observed erase run hT
  unfold Impl.t_21cf_c53 at run
  orsd
  orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[99]? = some Impl.t_4430_c99 from rfl] at hg
  cases hg
  rcases V22TransferReach.setter_reach_observed erase run hT with source | ⟨_, _, _, run⟩
  · exact .inr (.inl source)
  unfold Impl.t_21d4_c53 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[100]? = some Impl.t_4163_c100 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, run⟩ := V22TransferReach.sub_reach_observed erase run hT
  exact minter_reach_observed erase run hT cont

/-- The checked dispatcher selects the original mint ABI wrapper. -/
theorem route_mint : SFunc.selWalk 0x40c10f19
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0x40, 0xc1, 0x0f, 0x19], 160) := by
  decide +kernel

/-- Follow every selected mint store through the actual ABI and guard prefix. -/
theorem mint_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T := by
  unfold Impl.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0x40c10f19 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_mint run hT
  rw [show Impl.cert.prog[160]? = some Impl.t_07fb_c160 from rfl] at hg
  cases hg
  unfold Impl.t_07fb_c160 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0811_c160 at run
  orsd
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20] at run
  rw [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[53]? = some Impl.t_1ec5_c53 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [Impl.t_0428_c160], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold Impl.t_1ec5_c53 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_1f52_c53 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 3 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_1fba_c53 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_1fc4_c53 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_201a_c53 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_2024_c53 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_207a_c53 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_20e6_c53 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_213f_c53 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  exact body_reach_observed erase run hT cont

/-- The fixed supply and minter-store tails have distinct original source sites. -/
theorem supplyPattern_occurrences :
    BytePattern.occurrences (supplyLine.flatMap Ninst.toBytes) Impl.code.toList = [0x21b8] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem minterPattern_occurrences :
    BytePattern.occurrences (minterLine.flatMap Ninst.toBytes) Impl.code.toList = [0x21f5] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The setter's immediate return distinguishes it from the other two mint stores. -/
theorem setter_pc_ne_literals {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK Impl.code Impl.cert node κ)
    (tree : κ.f = .next (.reg .sstore) .ret) :
    node.pc ≠ 0x21b8 ∧ node.pc ≠ 0x21f5 := by
  have checked := ok.check
  rw [tree] at checked
  obtain ⟨_, a, later⟩ := checkNode_nexts [.reg .sstore] .ret checked
  have byte : byteAt Impl.code (κ.pc + 1) = some (Jinst.toUInt8 .jump) := by
    rcases a with _ | ⟨_ | _ | _, a⟩ <;>
      simp only [checkNode, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at later
    exact later.1
  constructor
  · intro bad
    rw [← ok.pc_eq, bad] at byte
    have actual : byteAt Impl.code (0x21b8 + 1) = some 0x61 := by decide +kernel
    rw [actual] at byte
    contradiction
  · intro bad
    rw [← ok.pc_eq, bad] at byte
    have actual : byteAt Impl.code (0x21f5 + 1) = some 0x80 := by decide +kernel
    rw [actual] at byte
    contradiction

/-- Every selected successful store is literal supply or its actual mapping row.
The balance setter is distinguished from the other sites by checked return bytes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x40c10f19)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x21b8 ∧ write.key = 11) ∨
    (node.pc ≠ 0x21b8 ∧ node.pc ≠ 0x21f5 ∧
      write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.pc = 0x21f5 ∧ write.key = mapSlot root.sevm.caller.toB256 13 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.caller.toB256.toBytes ++ (13 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases mint_reach_observed (fun h => StepIn.toRun h) selected walk target with
    ⟨⟨other, keyStack⟩, ⟨tail, source⟩⟩ |
    ⟨⟨value, other, keyStack⟩, source, hash⟩ | ⟨⟨other, keyStack⟩, ⟨tail, source⟩, hash⟩
  · exact .inl ⟨ok.pc_eq_of_prefix_singleton supplyLine tail source
      (suffix := []) (by simp only [List.append_nil]) (by decide) supplyPattern_occurrences,
      (List.cons.inj (stack.symm.trans keyStack)).1⟩
  · obtain ⟨notSupply, notMinter⟩ := setter_pc_ne_literals ok source
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr (.inl ⟨notSupply, notMinter, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)
  · have location := ok.pc_eq_of_prefix_singleton minterLine tail source
      (suffix := []) (by simp only [List.append_nil]) (by decide) minterPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr (.inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)

end Blanc.Lift.Usdc.V22MintReach
