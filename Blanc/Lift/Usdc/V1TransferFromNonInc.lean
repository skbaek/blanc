import Blanc.Lift.Usdc.V1TransferFromReach
import Blanc.Lift.Usdc.V1TransferFromNonIncReach

/-! Actual V1 transferFrom allowance stores do not increase their current cell. -/
namespace Blanc.Lift.Usdc.V1TransferFromNonInc

open Jaune Blanc Blanc.Lift

/-- The actual allowance write is bounded by the same node's current storage cell.
The reload follows both balance writes, so this needs no separation between their keys. -/
theorem allowanceStore_nonInc {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (atSite : node.pc = 0x14e2) :
    write.value.toNat ≤ ((node.devm.getStor root.sevm.currentTarget).get write.key).toNat := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  obtain ⟨base, a, c, d, e, amount, rest, mem, gas, saved, body, cont⟩ :=
    V1TransferFromReach.transferFrom_body_reach_observed (fun h => StepIn.toRun h)
      selected walk target
  rcases V1TransferFromNonIncReach.body_reach_nonInc (fun h => StepIn.toRun h)
      body target cont with ⟨tail, source⟩ | ⟨tail, source⟩ | ⟨value, tail, operands, bound⟩
  · have location := ok.pc_eq_of_prefix_singleton
      [.reg .sstore, .reg .pop, .push [0x13, 0x91] (by decide)] tail source
      (suffix := []) (by decide +kernel) (by decide +kernel)
      V1TransferFromReach.owner_pattern_occurrences
    omega
  · have location := ok.pc_eq_of_prefix_singleton
      [.reg .sstore, .reg .pop, .push [0x14, 0x63] (by decide)] tail source
      (suffix := []) (by decide +kernel) (by decide +kernel)
      V1TransferFromReach.recipient_pattern_occurrences
    omega
  · have keys := List.cons.inj (stack.symm.trans operands)
    have values := (List.cons.inj keys.2).1
    rw [keys.1, values]
    exact bound

/-- Three actual store sites, retaining the existing key and original hash witnesses.
Only the allowance alternative adds its same-node nonincrease conclusion. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x23b872dd)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.pc = 0x133e ∧ write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      KeccakBefore root node ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes)
        0x133b) ∨
    (node.pc = 0x13d3 ∧ write.key = mapSlot (Sevm.dataWord root.sevm 36).toAdr.toB256 9 ∧
      KeccakBefore root node ((Sevm.dataWord root.sevm 36).toAdr.toB256.toBytes ++ (9 : B256).toBytes)
        0x13d0) ∨
    (node.pc = 0x14e2 ∧ write.key = mapSlot root.sevm.caller.toB256
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10) ∧
      KeccakBefore root node ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        0x14a2 ∧
      KeccakBefore root node (root.sevm.caller.toB256.toBytes ++
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes) 0x14df ∧
      KeccakPairBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (10 : B256).toBytes)
        (root.sevm.caller.toB256.toBytes ++
          (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 10).toBytes) ∧
      write.value.toNat ≤ ((node.devm.getStor root.sevm.currentTarget).get write.key).toNat) := by
  rcases V1TransferFromReach.successfulSstore_source pc code hsg chain selected found with
    owner | recipient | ⟨location, key, inner, outer, ordered⟩
  · exact .inl owner
  · exact .inr (.inl recipient)
  · exact .inr (.inr ⟨location, key, inner, outer, ordered,
      allowanceStore_nonInc pc code hsg chain selected found location⟩)

end Blanc.Lift.Usdc.V1TransferFromNonInc
