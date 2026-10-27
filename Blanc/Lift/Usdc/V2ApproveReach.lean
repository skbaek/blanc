import Blanc.Lift.CursorKeccakOrder
import Blanc.Lift.Usdc.ImplV2.Check
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.WalkCutKit

/-! Actual V2 approve stores and the ordered hashes that compute their keys. -/
namespace Blanc.Lift.Usdc.V2ApproveReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

/-- The actual allowance key, with the two hash observations joined by their prefix. -/
def OrderedObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (spender : Adr) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = mapSlot spender.toB256 (mapSlot sevm.caller.toB256 10) :: rest) ∧
  ObservedKeccakPair Q observe ImplV2.cert.prog sevm
    (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
    (spender.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes)

/-- Abstract the guard memory before observing the two mapping hashes. -/
theorem body_reach_ordered {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value x z : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: a.toB256 :: sevm.caller.toB256 :: x :: a.toB256 ::
        sevm.caller.toB256 :: z :: value :: a.toB256 :: S) M G, ImplV2.t_3e89_c81, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    OrderedObservedSource Q observe sevm a T := by
  unfold ImplV2.t_3e89_c81 at run
  orsd
  iterate 4 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 12 orsx
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
    (input := sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run firstHash
  rw [Mem.read_two_word_writes_at_raw] at run firstHash
  have run := run.withPrefix
  iterate 3 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 9 orsx
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++
      (mapSlot sevm.caller.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact ⟨⟨_, rfl⟩, _, firstHash, secondHash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim


/-- The checked dispatcher routes approve through its original ABI wrapper. -/
theorem route_approve : SFunc.selWalk 0x095ea7b3
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3], 149) := by
  decide +kernel

/-- Follow the selected prefix to its store; the final frame outcome is unrestricted. -/
theorem approve_reach_ordered {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : OrderedObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T := by
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
      0x095ea7b3 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_approve run hT
  rw [show ImplV2.cert.prog[149]? = some ImplV2.t_03ce_c149 from rfl] at hg
  cases hg
  unfold ImplV2.t_03ce_c149 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_03e4_c149 at run
  orsd
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20] at run
  rw [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[61]? = some ImplV2.t_0f56_c61 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_0407_c149], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2.t_0f56_c61 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_0fe3_c61 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_104c_c61 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_10cd_c61 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[81]? = some ImplV2.t_3db1_c81 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_10d8_c61, ImplV2.t_0407_c149], f.sstoreFreeIn [] = true := by
    intro f member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  unfold ImplV2.t_3db1_c81 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_3e1d_c81 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_ordered erase run hT cont

/-- The actual successful store fixes the key and supplies its earlier ordered hashes. -/
theorem successfulSstore_ordered_hashes {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256
      (mapSlot root.sevm.caller.toB256 10) ∧
      KeccakPairBefore root node
        (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
          (mapSlot root.sevm.caller.toB256 10).toBytes) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
    ImplV2.cert.prog root.sevm ⟨root.devm, ImplV2.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  obtain ⟨⟨other, keyStack⟩, hashes⟩ :=
    approve_reach_ordered (fun h => StepIn.toRun h) selected walk target
  have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
  exact ⟨keyEq, hashes.actual⟩

end Blanc.Lift.Usdc.V2ApproveReach
