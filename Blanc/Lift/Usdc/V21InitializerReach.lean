import Blanc.Lift.Usdc.OldTransferFromCallee
import Blanc.Lift.Usdc.V2_1TransferReach
import Blanc.Lift.FrameSkip

/-! Original V2.1 initializeV2_1 stores and their successful hash inputs. -/
namespace Blanc.Lift.Usdc.V21InitializerReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

def blacklistLine : List Ninst := [.reg .sstore, .push [0x12] (by decide), .reg (.dup 0)]

def AfterSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = 18 :: rest) ∨
  ((∃ rest, T.d.stack = mapSlot sevm.currentTarget.toB256 3 :: rest) ∧
    (∃ tail, T.f = blacklistLine.foldr SFunc.next tail) ∧
    ObservedKeccak Q observe sevm
      (sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes) (fun _ => True))

/-- The suffix after the optional transfer writes the actual target blacklist row
and fixed version slot. Its blacklist hash belongs to this original walk. -/
theorem after_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y : B256} {S : List B256} {M : Mem} {G : Nat}
    {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (x :: y :: S) M G, ImplV2_1.t_1583_c54, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AfterSource Q observe sevm T := by
  unfold ImplV2_1.t_1583_c54 at run
  orsd
  iterate 12 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes)
    (shape := fun _ => True) (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  orsx
  orsld
  iterate 8 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 2 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨_, rfl⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The internal transfer either contains the selected store or actually returns
with the checked caller stack before the blacklist/version suffix. -/
theorem body_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {tag : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (recipient.toB256 :: tag :: S) M G, ImplV2_1.t_1550_c54, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    OldTransferBodyReach.BoundedObservedSource Q observe sevm sevm.currentTarget recipient T ∨
      AfterSource Q observe sevm T := by
  unfold ImplV2_1.t_1550_c54 at run
  orsd
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_1562_c54 at run
  orsd
  iterate 11 orsx
  orsld
  rename_i loaded amount gas
  iterate 3 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact .inr (after_source erase run hT cont)
  unfold ImplV2_1.t_1579_c54 at run
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[73]? = some ImplV2_1.t_3b21_c73 from rfl] at hg
  cases hg
  rcases OldTransferFromCallee.body_bounded_source_or_return
      (version := .v2_1) (by decide) erase run hT with source | ⟨returned, callee, _, later⟩
  · exact .inl source
  obtain ⟨Y, stack, length⟩ := callee.entry_stack_below_noStateGas erase ImplV2_1.cert_check hsg
    (k := 73) (ρ := 0x1583)
    (X := [amount, recipient.toB256, sevm.currentTarget.toB256, 0x1583])
    (R := amount :: recipient.toB256 :: tag :: S)
    (show ImplV2_1.cert.entries[73]? = some ⟨0x3b21, [.unk, .unk, .unk, .ret], 0⟩ from rfl)
    (show ImplV2_1.cert.prog[73]? = some ImplV2_1.t_3b21_c73 from rfl) rfl
    (by exact .cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  have empty : Y = [] := by
    cases Y with
    | nil => rfl
    | cons head tail => simp only [List.length_cons] at length; omega
  simp only [empty, List.nil_append] at stack
  rw [St.self stack rfl] at later
  exact .inr (after_source erase later hT cont)

/-- Exact selector routing through the inherited initializer wrapper. -/
theorem route_initializer : SFunc.selWalk 0x2fc81e09
    (.next (.reg (.dup 0)) (.next (.push [0x7f, 0x2e, 0xec, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xb2] (by decide))
        (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))) =
    .inl (Bytes.toB256 [0x2f, 0xc8, 0x1e, 0x09], 138) := by
  decide +kernel

/-- Original entry and ABI decoding reach either the transfer's balance store or
the initializer suffix, with no assumption about eventual frame success. -/
theorem entry_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (selected : Blanc.Sevm.selector sevm = 0x2fc81e09)
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b S M G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    OldTransferBodyReach.BoundedObservedSource Q observe sevm sevm.currentTarget
      (Sevm.dataWord sevm 4).toAdr T ∨ AfterSource Q observe sevm T := by
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
      0x2fc81e09 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_initializer run hT
  rw [show ImplV2_1.cert.prog[138]? = some ImplV2_1.t_04ca_c138 from rfl] at hg
  cases hg
  unfold ImplV2_1.t_04ca_c138 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_04e0_c138 at run
  orsd
  iterate 5 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[54]? = some ImplV2_1.t_1550_c54 from rfl] at hg
  cases hg
  apply body_source erase hsg run hT
  intro f member
  have same := List.mem_singleton.mp member
  subst f
  decide +kernel

/-- The initializer's blacklist writer is uniquely identified by its byte tail. -/
theorem blacklistPattern_occurrences :
    BytePattern.occurrences (blacklistLine.flatMap Ninst.toBytes) ImplV2_1.code.toList = [0x15c0] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- Every original successful store retains its fixed slot or exact mapping key and hash. -/
theorem successfulSstore_all_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 18 ∨
    (node.pc = 0x3cd2 ∧
      write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∧
      write.key = mapSlot root.sevm.currentTarget.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.currentTarget.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.pc = 0x3d11 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.pc = 0x15c0 ∧ write.key = mapSlot root.sevm.currentTarget.toB256 3 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2_1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2_1.code ImplV2_1.cert root node)
    ImplV2_1.cert.prog root.sevm ⟨root.devm, ImplV2_1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases entry_source (fun h => StepIn.toRun h) hsg selected walk target with
    source | afterSource
  · rcases source with ⟨⟨value, other, keyStack, bound⟩, ⟨tail, shape⟩, hash⟩ |
        ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩
    · have same := List.cons.inj (stack.symm.trans keyStack)
      have valueEq := (List.cons.inj same.2).1
      rw [← same.1, ← valueEq] at bound
      rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
      have location := ok.pc_eq_of_prefix_singleton OldTransferBodyReach.ownerLine tail shape
        (suffix := []) (by simp only [List.append_nil]) (by decide)
        V2_1TransferReach.ownerPattern_occurrences
      obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
        hash.actual
      exact .inr (.inl ⟨location, bound, same.1,
        _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)
    · have location := ok.pc_eq_of_prefix_singleton OldTransferBodyReach.recipientLine tail shape
        (suffix := []) (by simp only [List.append_nil]) (by decide)
        V2_1TransferReach.recipientPattern_occurrences
      obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
        hash.actual
      exact .inr (.inr (.inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
        _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩))
  · rcases afterSource with ⟨other, keyStack⟩ | ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩
    · exact .inl (List.cons.inj (stack.symm.trans keyStack)).1
    · have location := ok.pc_eq_of_prefix_singleton blacklistLine tail shape
        (suffix := []) (by simp only [List.append_nil]) (by decide) blacklistPattern_occurrences
      obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
        hash.actual
      exact .inr (.inr (.inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
        _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩))

/-- Every original successful store is fixed, bounded at that same node, or has
its own recipient-balance or target-blacklist hash before the store. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 18 ∨
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
    (node.pc = 0x3d11 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.pc = 0x15c0 ∧ write.key = mapSlot root.sevm.currentTarget.toB256 3 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.currentTarget.toB256.toBytes ++ (3 : B256).toBytes) hashPc) := by
  rcases successfulSstore_all_source pc code hsg chain selected found with
    fixed | ⟨_, bound, _, _⟩ | source
  · exact .inl fixed
  · exact .inr (.inl bound)
  · exact .inr (.inr source)

end Blanc.Lift.Usdc.V21InitializerReach
