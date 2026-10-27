import Blanc.Lift.Usdc.OldTransferFromAllowance
import Blanc.Lift.Usdc.V2TransferFromEntry
import Blanc.Lift.FrameSkip

/-! The post-transfer allowance write is bounded at its own original pre-state. -/
namespace Blanc.Lift.Usdc.V2TransferFromContinuation

open Jaune Blanc Blanc.Lift V2TransferFromEntry
variable {observe : Conf → Conf → Prop}

/-- The registered runtime has one final transferFrom allowance-store prefix. -/
theorem allowancePattern_occurrences :
    BytePattern.occurrences (OldTransferFromAllowance.storeLine.flatMap Ninst.toBytes)
      ImplV2.code.toList = [0x14e9] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel


/-- The final allowance tail writes the value bounded against this exact storage base. -/
theorem tail_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount value : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: guardedStack sevm owner recipient amount S) M G,
        ImplV2.t_14b8_c59, K⟩ T)
    (bounded : value.toNat ≤ (b.getStorVal sevm.currentTarget
      (mapSlot sevm.caller.toB256 (mapSlot owner.toB256 10))).toNat)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  exact OldTransferFromAllowance.tail_nonInc erase run bounded hT cont

/-- Reload after the balance transfer, then use the actual checked subtraction return.
Even an allowance/balance hash alias cannot invalidate this same-node bound. -/
theorem allowance_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (guardedStack sevm owner recipient amount S) M G,
        ImplV2.t_147d_c59, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  exact OldTransferFromAllowance.allowance_nonInc (version := .v2) (by decide) erase run hT cont

/-- Original entry retains allowance and both balance sources, with no
final-frame-success or hash-separation premise. -/
theorem entry_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (selected : Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    OldTransferFromAllowance.StoreSource Q observe ImplV2.cert.prog sevm
      (Sevm.dataWord sevm 4).toAdr T ∨
    OldTransferBodyReach.BoundedObservedSource Q observe sevm
      (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr T := by
  obtain ⟨R, b', M', G', body⟩ := entry_to_body erase selected run hT
  rcases V2TransferFromCallee.body_bounded_source_or_return erase body hT with
    source | ⟨returned, callee, _, later⟩
  · exact .inr source
  obtain ⟨Y, stack, length⟩ := callee.entry_stack_below_noStateGas erase ImplV2.cert_check hsg
    (k := 74) (ρ := 0x147d)
    (X := [Sevm.dataWord sevm 68, (Sevm.dataWord sevm 36).toAdr.toB256,
      (Sevm.dataWord sevm 4).toAdr.toB256, 0x147d])
    (R := guardedStack sevm (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) R)
    (show ImplV2.cert.entries[74]? = some ⟨0x3ef8, [.unk, .unk, .unk, .ret], 0⟩ from rfl)
    (show ImplV2.cert.prog[74]? = some ImplV2.t_3ef8_c74 from rfl) rfl
    (by exact .cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  have empty : Y = [] := by
    cases Y with
    | nil => rfl
    | cons head tail => simp only [List.length_cons] at length; omega
  simp only [empty, List.nil_append] at stack
  rw [St.self stack rfl] at later
  apply Or.inl (OldTransferFromAllowance.allowance_source (version := .v2) (by decide) erase later hT ?_)
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
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    (∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat) ∨
    ((∃ rest, T.d.stack = mapSlot (Sevm.dataWord sevm 36).toAdr.toB256 9 :: rest) ∧
      (∃ tail, T.f = V2TransferReach.recipientLine.foldr SFunc.next tail) ∧
      ObservedKeccak Q observe sevm
        ((Sevm.dataWord sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)) := by
  rcases entry_source erase hsg selected run hT with ⟨value, rest, stack, bound, _⟩ | source
  · exact .inl ⟨_, value, rest, stack, bound⟩
  · rcases source with ⟨⟨value, rest, stack, bound⟩, _, _⟩ | recipient
    · exact .inl ⟨_, value, rest, stack, bound⟩
    · exact .inr recipient

/-- Every original successful store retains its exact key and earlier successful hashes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x14e9 ∧ write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∧
      write.key = mapSlot root.sevm.caller.toB256
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10) ∧
      KeccakPairBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        (root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes)) ∨
    (node.pc = 0x40a9 ∧ write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∧
      write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
      (node.pc = 0x40e8 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∧
        ∃ hashPc, KeccakBefore root node
          ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
    ImplV2.cert.prog root.sevm ⟨root.devm, ImplV2.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases entry_source (fun h => StepIn.toRun h) hsg selected walk target with
    ⟨value, other, shape, bound, ⟨tail, storeShape⟩, hashes⟩ | source
  · have location := ok.pc_eq_of_prefix_singleton OldTransferFromAllowance.storeLine tail storeShape
      (suffix := []) (by simp only [List.append_nil]) (by decide) allowancePattern_occurrences
    have same := List.cons.inj (stack.symm.trans shape)
    have keyEq := same.1
    have valueEq := (List.cons.inj same.2).1
    rw [← keyEq, ← valueEq] at bound
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
    exact .inl ⟨location, bound, keyEq, hashes.actual⟩
  rcases source with ⟨⟨value, other, keyStack, bound⟩, ⟨tail, shape⟩, hash⟩ | recipient
  · have location := ok.pc_eq_of_prefix_singleton OldTransferBodyReach.ownerLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide) V2TransferReach.ownerPattern_occurrences
    have same := List.cons.inj (stack.symm.trans keyStack)
    have keyEq := same.1
    have valueEq := (List.cons.inj same.2).1
    rw [← keyEq, ← valueEq] at bound
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr (.inl ⟨location, bound, keyEq,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)
  obtain ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩ := recipient
  have location := ok.pc_eq_of_prefix_singleton V2TransferReach.recipientLine tail shape
    (suffix := []) (by simp only [List.append_nil]) (by decide) V2TransferReach.recipientPattern_occurrences
  obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
    hash.actual
  exact .inr (.inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
    _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)

/-- Original credit-or-nonincrease interface, projected from all-write sources. -/
theorem successfulSstore_credit_or_nonInc {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
      (node.pc = 0x40e8 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∧
        ∃ hashPc, KeccakBefore root node
          ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
  rcases successfulSstore_source pc code hsg chain selected found with
    ⟨_, bound, _, _⟩ | ⟨_, bound, _, _⟩ | recipient
  · exact .inl bound
  · exact .inl bound
  · exact .inr recipient

end Blanc.Lift.Usdc.V2TransferFromContinuation
