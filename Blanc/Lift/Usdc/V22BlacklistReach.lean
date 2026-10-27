import Blanc.Lift.Usdc.ModernCallerReach

/-! Original packed-balance keys and successful hashes for V2_2 blacklist updates. -/
namespace Blanc.Lift.Usdc.V22BlacklistReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

/-- The shared packed-word store computes the actual address/base-9 key before writing. -/
theorem store_key_hash {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value flag : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: flag :: a.toB256 :: S) M G, Impl.t_4d23_c10, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    (∃ rest, T.d.stack = mapSlot a.toB256 9 :: rest) ∧
      ObservedKeccak Q observe sevm (a.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
  unfold Impl.t_4d23_c10 at run
  orsd
  iterate 4 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 9 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 3 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact ⟨⟨_, rfl⟩, hash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- Either flag branch reaches the shared store; the false branch's balance read keeps the address. -/
theorem setState_key_hash {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {flag : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (flag :: a.toB256 :: S) M G, Impl.t_4cc7_c109, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    (∃ rest, T.d.stack = mapSlot a.toB256 9 :: rest) ∧
      ObservedKeccak Q observe sevm (a.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
  unfold Impl.t_4cc7_c109 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · unfold Impl.t_4ccd_c109 at run
    iterate 3 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    change some Impl.t_41da_c96 = some g at hg
    cases hg
    unfold Impl.t_41da_c96 at run
    orsd
    iterate 12 orsx
    orsld
    iterate 3 orsx
    obtain ⟨f, K', b', G', same, run⟩ := ObservedReach.rs_retM run hT
    obtain ⟨rfl, rfl⟩ := List.cons.inj same
    unfold Impl.t_4cd5_c109 at run
    orsd
    orsx
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨next, ⟨step, _⟩, suffix⟩
    · obtain ⟨_, impossible⟩ := hT
      cases impossible
    · cases step with
      | jump t hk pop =>
        change some Impl.t_4d23_c10 = some _ at hk
        cases hk
        obtain ⟨_, same⟩ := St.of_pop1 pop
        exact store_key_hash erase (same ▸ suffix) hT cont
  · unfold Impl.t_4cda_c109 at run
    orsd
    iterate 13 orsx
    orsld
    iterate 2 orsx
    exact store_key_hash erase run hT cont

def wrapper (blocked : Bool) : SFunc :=
  if blocked then Impl.t_11c1_c127 else Impl.t_0456_c174

/-- The public ABI and role guard preserve the calldata address through both internal calls. -/
theorem wrapper_key_hash {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') (blocked : Bool)
    {sevm : Sevm} {b : Devm} {selector : B256} {S : List B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (selector :: S) M G, wrapper blocked, []⟩ T) (hT : AtSstore T) :
    (∃ rest, T.d.stack = mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 9 :: rest) ∧
      ObservedKeccak Q observe sevm
        ((Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
  cases blocked
  all_goals
    simp only [wrapper, Bool.false_eq_true, ↓reduceIte] at run
    first
    | unfold Impl.t_0456_c174 at run
    | unfold Impl.t_11c1_c127 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold Impl.t_046c_c174 at run
    | unfold Impl.t_11d7_c127 at run
    orsd
    iterate 4 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      ff20_and_word] at run
    orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | change some Impl.t_137a_c67 = some g at hg
    | change some Impl.t_3d50_c17 = some g at hg
    cases hg
    first
    | unfold Impl.t_137a_c67 at run
    | unfold Impl.t_3d50_c17 at run
    orsd
    orsx
    orsld
    iterate 5 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (by intro f member; have same := List.mem_singleton.mp member; subst f; decide +kernel)).elim
    first
    | unfold Impl.t_13ea_c67 at run
    | unfold Impl.t_3dc0_c17 at run
    orsd
    iterate 3 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | change some Impl.t_3f5f_c104 = some g at hg
    | change some Impl.t_4224_c86 = some g at hg
    cases hg
    first
    | unfold Impl.t_3f5f_c104 at run
    | unfold Impl.t_4224_c86 at run
    orsd
    iterate 4 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    change some Impl.t_4cc7_c109 = some g at hg
    cases hg
    apply setState_key_hash erase run hT
    intro f member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel

def entry (blocked : Bool) : Nat := if blocked then 127 else 174

/-- Original selector routing reaches the matching public blacklist wrapper. -/
theorem reach_key_hash {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') (blocked : Bool)
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = if blocked then 0xf9f92be4 else 0x1a895266)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T) (hT : AtSstore T) :
    (∃ rest, T.d.stack = mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 9 :: rest) ∧
      ObservedKeccak Q observe sevm
        ((Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
  have routing : SFunc.selWalk (Blanc.Sevm.selector sevm) (ModernCallerReach.dispatch .v2_2) =
      .inl (Blanc.Sevm.selector sevm, entry blocked) := by
    rw [selected]
    cases blocked <;> decide +kernel
  have wrapperAt : Impl.cert.prog[entry blocked]? = some (wrapper blocked) := by
    cases blocked <;> rfl
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      Blanc.Sevm.selector sevm := rfl
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
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase routing run hT
  rw [wrapperAt] at hg
  cases hg
  exact wrapper_key_hash erase blocked run hT

/-- The written balance key and its successful hash come from the same original prefix. -/
theorem successfulSstore_key_hash {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x1a895266 ∨
      Blanc.Sevm.selector root.sevm = 0xf9f92be4)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self' root.devm] at reach
  have result : (∃ other, node.devm.stack =
      mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 :: other) ∧
      ObservedKeccak (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node) root.sevm
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True) := by
    rcases selected with selected | selected
    · exact reach_key_hash (fun h => StepIn.toRun h) false selected reach target
    · exact reach_key_hash (fun h => StepIn.toRun h) true selected reach target
  obtain ⟨⟨other, shape⟩, hash⟩ := result
  have keyEq := (List.cons.inj (stack.symm.trans shape)).1
  obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
    _, _, hashStack, read⟩ := hash.actual
  exact ⟨keyEq, occurrence.node.pc, occurrence, next, rfl, instruction, result,
    reached, edge, suffix, hashStack, read⟩

end Blanc.Lift.Usdc.V22BlacklistReach
