import Blanc.Lift.Usdc.OldTransferFromAllowance
import Blanc.Lift.FrameSkip

/-! Original V2.1 transferFrom increases retain their own recipient hash. -/
namespace Blanc.Lift.Usdc.V2_1TransferFromContinuation
open Jaune Blanc Blanc.Lift OldTransferFromEntry
variable {observe : Conf → Conf → Prop}

/-- Exact registered-runtime scan identifies the original recipient store. -/
theorem recipientPattern_occurrences :
    BytePattern.occurrences (OldTransferBodyReach.recipientLine.flatMap Ninst.toBytes)
      ImplV2_1.code.toList = [0x3d11] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- Original entry retains allowance and both balance sources, with no
final-frame-success or hash-separation premise. -/
theorem entry_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (selected : Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b S M G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    OldTransferFromAllowance.StoreSource Q observe ImplV2_1.cert.prog sevm
      (Sevm.dataWord sevm 4).toAdr T ∨
    OldTransferBodyReach.BoundedObservedSource Q observe sevm
      (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr T := by
  obtain ⟨R, b', M', G', body⟩ := entry_to_body (version := .v2_1) (by decide) erase selected run hT
  rcases OldTransferFromCallee.body_bounded_source_or_return (version := .v2_1) (by decide) erase body hT with
    source | ⟨returned, callee, _, later⟩
  · exact .inr source
  obtain ⟨Y, stack, length⟩ := callee.entry_stack_below_noStateGas erase ImplV2_1.cert_check hsg
    (k := 73) (ρ := 0x1375)
    (X := [Sevm.dataWord sevm 68, (Sevm.dataWord sevm 36).toAdr.toB256,
      (Sevm.dataWord sevm 4).toAdr.toB256, 0x1375])
    (R := guardedStack sevm (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) R)
    (show ImplV2_1.cert.entries[73]? = some ⟨0x3b21, [.unk, .unk, .unk, .ret], 0⟩ from rfl)
    (show ImplV2_1.cert.prog[73]? = some ImplV2_1.t_3b21_c73 from rfl) rfl
    (by exact .cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  have empty : Y = [] := by
    cases Y with
    | nil => rfl
    | cons head tail => simp only [List.length_cons] at length; omega
  simp only [empty, List.nil_append] at stack
  rw [St.self stack rfl] at later
  apply Or.inl (OldTransferFromAllowance.allowance_source (version := .v2_1) (by decide) erase later hT ?_)
  intro f member
  have same := List.mem_singleton.mp member
  subst f
  decide +kernel

/-- Original credit-or-nonincrease interface, projected from all-write sources. -/
theorem entry_credit_or_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (selected : Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b S M G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    (∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat) ∨
    ((∃ rest, T.d.stack = mapSlot (Sevm.dataWord sevm 36).toAdr.toB256 9 :: rest) ∧
      (∃ tail, T.f = OldTransferBodyReach.recipientLine.foldr SFunc.next tail) ∧
      ObservedKeccak Q observe sevm
        ((Sevm.dataWord sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) := by
  rcases entry_source erase hsg selected run hT with ⟨value, rest, stack, bound, _⟩ | source
  · exact .inl ⟨_, value, rest, stack, bound⟩
  · rcases source with ⟨⟨value, rest, stack, bound⟩, _, _⟩ | recipient
    · exact .inl ⟨_, value, rest, stack, bound⟩
    · exact .inr recipient

/-- Every original successful store retains its exact key and earlier successful hashes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∧
      write.key = mapSlot root.sevm.caller.toB256
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10) ∧
      KeccakPairBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        (root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes)) ∨
    (write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∧
      write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
      (node.pc = 0x3d11 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∧
        ∃ hashPc, KeccakBefore root node
          ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
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
    ⟨value, other, shape, bound, hashes⟩ | source
  · have same := List.cons.inj (stack.symm.trans shape)
    have keyEq := same.1
    have valueEq := (List.cons.inj same.2).1
    rw [← keyEq, ← valueEq] at bound
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
    exact .inl ⟨bound, keyEq, hashes.actual⟩
  rcases source with ⟨⟨value, other, keyStack, bound⟩, _, hash⟩ | recipient
  · have same := List.cons.inj (stack.symm.trans keyStack)
    have keyEq := same.1
    have valueEq := (List.cons.inj same.2).1
    rw [← keyEq, ← valueEq] at bound
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr (.inl ⟨bound, keyEq,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)
  obtain ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩ := recipient
  have location := ok.pc_eq_of_prefix_singleton OldTransferBodyReach.recipientLine tail shape
    (suffix := []) (by simp only [List.append_nil]) (by decide) recipientPattern_occurrences
  obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
    hash.actual
  exact .inr (.inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
    _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)

/-- Original credit-or-nonincrease interface, projected from all-write sources. -/
theorem successfulSstore_credit_or_nonInc {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      (node.pc = 0x3d11 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∧
        ∃ hashPc, KeccakBefore root node
          ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
  rcases successfulSstore_source pc code hsg chain selected found with
    ⟨bound, _, _⟩ | ⟨bound, _, _⟩ | recipient
  · exact .inl bound
  · exact .inl bound
  · exact .inr recipient

end Blanc.Lift.Usdc.V2_1TransferFromContinuation
