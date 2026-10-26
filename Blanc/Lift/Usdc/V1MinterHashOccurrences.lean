import Blanc.Lift.Usdc.V1MinterReach
import Blanc.Lift.Usdc.V1ConfigureMinterReach

/-! Actual successful V1 minter hashes, ordered before the reached raw store.
Each alternative retains its own exact two-word input and the original stop. -/
namespace Blanc.Lift.Usdc.V1MinterHashOccurrences

open Jaune Blanc Blanc.Lift

/-- The store pc/key and its own earlier successful hash are paired in each branch. -/
def RemoveHashSource (root node : Exec.Deriv) (a : Adr) (key : B256) : Prop :=
  (node.pc = 0x160b ∧ key = mapSlot a.toB256 12 ∧
    KeccakBefore root node (a.toB256.toBytes ++ (12 : B256).toBytes) 0x15f5) ∨
  (node.pc = 0x1650 ∧ key = mapSlot a.toB256 13 ∧
    KeccakBefore root node (a.toB256.toBytes ++ (13 : B256).toBytes) 0x164d)

/-- Read both hash pcs from their original checked hash cursors, using the accepted store anchors. -/
theorem remove_hashes_at_cursor {root node : Exec.Deriv} {κ : Cursor} {a : Adr}
    (ok : CursorOK ImplV1.code ImplV1.cert node κ)
    (source : V1MinterReach.ObservedSource (StepIn root)
      (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node) root.sevm a (κ.conf node.devm))
    {key value : B256} {rest : List B256}
    (stack : node.devm.stack = key :: value :: rest) : RemoveHashSource root node a key := by
  rcases source with ⟨⟨⟨tail, tree⟩, ⟨other, keyStack⟩⟩, hash⟩ |
    ⟨⟨⟨tail, bs, fits, width, tree⟩, ⟨other, keyStack⟩⟩, hash⟩
  · have keyEq : key = mapSlot a.toB256 12 := (List.cons.inj (stack.symm.trans keyStack)).1
    have storePc := ImplV1.pc_eq_160b_of_store_tail ok tree
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton packedBoolHashLead
      [.reg .sstore, .reg .pop, .push [0x00] (by decide)] hashTail hashTree
      (suffix := []) (by decide +kernel)
      ImplV1.minter160bPattern_ne_nil ImplV1.minter160bPattern_occurrences
    rw [packedBoolHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x15f5 := by omega
    exact .inl ⟨storePc, keyEq, occurrence, next, hashPc, instruction, result,
      reached, edge, suffix, hashStack, read⟩
  · have keyEq : key = mapSlot a.toB256 13 := (List.cons.inj (stack.symm.trans keyStack)).1
    have storePc := ImplV1.pc_eq_1650_of_store_tail ok fits width tree
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashBytes, hashFits, hashWidth, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
      [.reg .sstore, .reg .pop, .reg (.dup 1), .push hashBytes hashFits]
      hashTail hashTree (suffix := hashBytes) (by
        simp only [List.flatMap_cons, List.flatMap_nil, Ninst.toBytes, pushToB8L,
          pushToB8, List.append_nil]
        rw [hashWidth]
        rfl) ImplV1.minter1650Pattern_ne_nil ImplV1.minter1650Pattern_occurrences
    rw [wordStoreHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x164d := by omega
    exact .inr ⟨storePc, keyEq, occurrence, next, hashPc, instruction, result,
      reached, edge, suffix, hashStack, read⟩

/-- One synchronized raw-prefix traversal supplies the final cursor and every retained hash edge. -/
theorem remove_raw_store_hashes {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x3092afd5)
    (decoded : Ninst.At node.sevm.code node.pc (.reg .sstore))
    {key value : B256} {rest : List B256}
    (stack : node.devm.stack = key :: value :: rest) :
    ∃ κ, CursorOK ImplV1.code ImplV1.cert node κ ∧
      ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
        ImplV1.cert.prog root.sevm ((Cursor.start ImplV1.cert).conf root.devm) (κ.conf node.devm) ∧
      V1MinterReach.ActualRemoveSource (Sevm.dataWord root.sevm 4).toAdr node κ key ∧
      RemoveHashSource root node (Sevm.dataWord root.sevm 4).toAdr key := by
  obtain ⟨κ, reach, ok⟩ := observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  have source := V1MinterReach.remove_reach_observed (fun h => StepIn.toRun h) selected walk target
  exact ⟨κ, ok, reach, V1MinterReach.source_at_cursor ok source.source stack,
    remove_hashes_at_cursor ok source stack⟩

/-- The executable successful-store recognizer supplies the same actual store and ordered hashes. -/
theorem remove_successfulSstore_hashes {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ κ, CursorOK ImplV1.code ImplV1.cert node κ ∧
      ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
        ImplV1.cert.prog root.sevm ((Cursor.start ImplV1.cert).conf root.devm) (κ.conf node.devm) ∧
      V1MinterReach.ActualRemoveSource (Sevm.dataWord root.sevm 4).toAdr node κ write.key ∧
      RemoveHashSource root node (Sevm.dataWord root.sevm 4).toAdr write.key := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  exact remove_raw_store_hashes pc code hsg chain selected decoded stack

/-- The store pc/key and its own earlier successful hash are paired in each branch. -/
def ConfigureHashSource (root node : Exec.Deriv) (a : Adr) (key : B256) : Prop :=
  (node.pc = 0x20b2 ∧ key = mapSlot a.toB256 12 ∧
    KeccakBefore root node (a.toB256.toBytes ++ (12 : B256).toBytes) 0x209c) ∨
  (node.pc = 0x20f6 ∧ key = mapSlot a.toB256 13 ∧
    KeccakBefore root node (a.toB256.toBytes ++ (13 : B256).toBytes) 0x20f3)

/-- Read both hash pcs from their original checked hash cursors, using the accepted store anchors. -/
theorem configure_hashes_at_cursor {root node : Exec.Deriv} {κ : Cursor} {a : Adr}
    (ok : CursorOK ImplV1.code ImplV1.cert node κ)
    (source : V1ConfigureMinterReach.ObservedSource (StepIn root)
      (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node) root.sevm a (κ.conf node.devm))
    {key value : B256} {rest : List B256}
    (stack : node.devm.stack = key :: value :: rest) : ConfigureHashSource root node a key := by
  rcases source with ⟨⟨⟨tail, tree⟩, ⟨other, keyStack⟩⟩, hash⟩ |
    ⟨⟨⟨tail, bs, fits, width, tree⟩, ⟨other, keyStack⟩⟩, hash⟩
  · have keyEq : key = mapSlot a.toB256 12 := (List.cons.inj (stack.symm.trans keyStack)).1
    have storePc := ImplV1.pc_eq_20b2_of_store_tail ok tree
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton packedBoolHashLead
      [.reg .sstore, .reg .pop, .reg (.dup 1), .push [0x0d] (by decide)] hashTail hashTree
      (suffix := []) (by decide +kernel)
      ImplV1.minter20b2Pattern_ne_nil ImplV1.minter20b2Pattern_occurrences
    rw [packedBoolHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x209c := by omega
    exact .inl ⟨storePc, keyEq, occurrence, next, hashPc, instruction, result,
      reached, edge, suffix, hashStack, read⟩
  · have keyEq : key = mapSlot a.toB256 13 := (List.cons.inj (stack.symm.trans keyStack)).1
    have storePc := ImplV1.pc_eq_20f6_of_store_tail ok fits width tree
    obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
      placed, ⟨hashTail, hashBytes, hashFits, hashWidth, hashTree⟩, hashStack, read⟩ := hash.actual
    have offset := placed.pc_add_eq_of_prefix_singleton wordStoreHashLead
      [.reg .sstore, .reg .pop, .reg (.dup 2), .push hashBytes hashFits]
      hashTail hashTree (suffix := hashBytes) (by
        simp only [List.flatMap_cons, List.flatMap_nil, Ninst.toBytes, pushToB8L,
          pushToB8, List.append_nil]
        rw [hashWidth]
        rfl) ImplV1.minter20f6Pattern_ne_nil ImplV1.minter20f6Pattern_occurrences
    rw [wordStoreHashLead_size] at offset
    have hashPc : occurrence.node.pc = 0x20f3 := by omega
    exact .inr ⟨storePc, keyEq, occurrence, next, hashPc, instruction, result,
      reached, edge, suffix, hashStack, read⟩

/-- One synchronized raw-prefix traversal supplies the final cursor and every retained hash edge. -/
theorem configure_raw_store_hashes {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x4e44d956)
    (decoded : Ninst.At node.sevm.code node.pc (.reg .sstore))
    {key value : B256} {rest : List B256}
    (stack : node.devm.stack = key :: value :: rest) :
    ∃ κ, CursorOK ImplV1.code ImplV1.cert node κ ∧
      ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
        ImplV1.cert.prog root.sevm ((Cursor.start ImplV1.cert).conf root.devm) (κ.conf node.devm) ∧
      V1ConfigureMinterReach.ActualConfigureSource (Sevm.dataWord root.sevm 4).toAdr node κ key ∧
      ConfigureHashSource root node (Sevm.dataWord root.sevm 4).toAdr key := by
  obtain ⟨κ, reach, ok⟩ := observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  have source := V1ConfigureMinterReach.configure_reach_observed (fun h => StepIn.toRun h) selected walk target
  exact ⟨κ, ok, reach, V1ConfigureMinterReach.source_at_cursor ok source.source stack,
    configure_hashes_at_cursor ok source stack⟩

/-- The executable successful-store recognizer supplies the same actual store and ordered hashes. -/
theorem configure_successfulSstore_hashes {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x4e44d956)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ κ, CursorOK ImplV1.code ImplV1.cert node κ ∧
      ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
        ImplV1.cert.prog root.sevm ((Cursor.start ImplV1.cert).conf root.devm) (κ.conf node.devm) ∧
      V1ConfigureMinterReach.ActualConfigureSource (Sevm.dataWord root.sevm 4).toAdr node κ write.key ∧
      ConfigureHashSource root node (Sevm.dataWord root.sevm 4).toAdr write.key := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  exact configure_raw_store_hashes pc code hsg chain selected decoded stack

end Blanc.Lift.Usdc.V1MinterHashOccurrences
