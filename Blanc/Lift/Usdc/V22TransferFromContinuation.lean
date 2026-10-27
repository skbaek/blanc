import Blanc.Lift.Usdc.V22TransferFromAllowance
import Blanc.Lift.FrameSkip

/-! Every V2.2 transferFrom store is an actual balance source or a nonincrease. -/
namespace Blanc.Lift.Usdc.V22TransferFromContinuation
open Jaune Blanc Blanc.Lift OldTransferFromEntry
variable {observe : Conf → Conf → Prop}

/-- Recover the original saved stack from the checked callee return, then reload
the allowance. Balance stores keep their own successful hash observations. -/
theorem entry_source_or_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (selected : Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    (∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat) ∨
    V22TransferReach.ObservedSource Q observe sevm
      (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr T := by
  obtain ⟨R, b', M', G', body⟩ := V22TransferFromEntry.entry_to_body erase selected run hT
  rcases V22TransferFromCallee.body_source_or_return erase body hT with
    source | ⟨returned, callee, _, later⟩
  · exact .inr source
  obtain ⟨Y, stack, length⟩ := callee.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 93) (ρ := 0x1678)
    (X := [Sevm.dataWord sevm 68, (Sevm.dataWord sevm 36).toAdr.toB256,
      (Sevm.dataWord sevm 4).toAdr.toB256, 0x1678])
    (R := guardedStack sevm (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) R)
    (show Impl.cert.entries[93]? = some ⟨0x3f98, [.unk, .unk, .unk, .ret], 0⟩ from rfl)
    (show Impl.cert.prog[93]? = some Impl.t_3f98_c93 from rfl) rfl
    (by exact .cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  have empty : Y = [] := by
    cases Y with
    | nil => rfl
    | cons head tail => simp only [List.length_cons] at length; omega
  simp only [empty, List.nil_append] at stack
  rw [St.self stack rfl] at later
  apply Or.inl (V22TransferFromAllowance.allowance_nonInc erase later hT ?_)
  intro f member
  have same := List.mem_singleton.mp member
  subst f
  decide +kernel

/-- Every original successful store is bounded at its own node or has the actual
balance setter tag, exact key and successful original hash before that store. -/
theorem successfulSstore_source_or_nonInc {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∨
    (node.devm.stack[2]? = some 0x40e8 ∧
      write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.devm.stack[2]? = some 0x40f9 ∧
      write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases entry_source_or_nonInc (fun h => StepIn.toRun h) hsg selected walk target with
    ⟨key, value, other, shape, bound⟩ | source
  · have same := List.cons.inj (stack.symm.trans shape)
    have keyEq := same.1
    have valueEq := (List.cons.inj same.2).1
    rw [← keyEq, ← valueEq] at bound
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
    exact .inl bound
  apply Or.inr
  rcases source with ⟨⟨value, other, keyStack⟩, _, hash⟩ | ⟨⟨value, other, keyStack⟩, _, hash⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
      (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr ⟨by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
      (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩

end Blanc.Lift.Usdc.V22TransferFromContinuation
