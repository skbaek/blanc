import Blanc.Lift.UniswapV2Pair.GetterStorageDispatch

/-! Successful pc-zero refinement and exact-gas liveness of the three mapping getters. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def SingleMappingGetter.storageGetter : SingleMappingGetter → StorageGetter
  | .balanceOf => .balanceOf
  | .nonces => .nonces

theorem SingleMappingGetter.storage_selector (s : SingleMappingGetter) :
    s.storageGetter.selector = s.selector := by cases s <;> rfl

theorem SingleMappingGetter.storage_entryTree (s : SingleMappingGetter) :
    s.storageGetter.entryTree = s.entryTree := by cases s <;> rfl

theorem SingleMappingGetter.source_value {st : State} {sevm : Sevm} {b : Devm}
    (s : SingleMappingGetter) (slots : s.SlotMatches st sevm b) :
    getterResult st (s.entry (mappingOwner sevm)) =
      some (b.getStorVal sevm.currentTarget (s.slot sevm)).toBytes := by
  cases s <;>
    simp only [SingleMappingGetter.SlotMatches] at slots <;>
    simp only [SingleMappingGetter.entry, getterResult, encodeWords, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, slots]

theorem singleMapping_pc0_exact {sevm : Sevm} {b : Devm} {G c : Nat}
    (s : SingleMappingGetter) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (s.slot sevm)) :
    SProg.RunExact cert.prog sevm
      (St b [] Mem.empty (G + c + 193 + s.storageGetter.dispatchGas))
      (getterWordPost (afterSload sevm b (s.slot sevm)) [0x039b, s.selector]
        (s.memory getterInitMemory (mappingOwner sevm).toB256)
        (b.getStorVal sevm.currentTarget (s.slot sevm)) G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have sel : Blanc.Sevm.selector sevm = s.storageGetter.selector := by
    rw [s.storage_selector]; exact selector
  have body := singleMapping_entry_exact (G := G) (sel := s.selector) s fork getterInitMemory_ptr guard cost
  rw [← s.storage_entryTree, ← s.storage_selector] at body
  rw [← s.storage_selector]
  exact getterStorage_dispatch_exact s.storageGetter value size sel body

theorem singleMapping_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (s : SingleMappingGetter) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      post.output = (b.getStorVal sevm.currentTarget (s.slot sevm)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  have sel : Blanc.Sevm.selector sevm = s.storageGetter.selector := by
    rw [s.storage_selector]; exact selector
  obtain ⟨_, run⟩ := getterStorage_selector_inv s.storageGetter sel run
  rw [s.storage_entryTree, s.storage_selector] at run
  obtain ⟨guard, d, eq, out, stor, logs⟩ := singleMapping_entry_inv s fork getterInitMemory_ptr run
  cases eq
  exact ⟨value, size, guard, out, stor, logs⟩

theorem singleMapping_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (s : SingleMappingGetter) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = s.selector) (slots : s.SlotMatches st sevm b)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      some post.output = getterResult st (s.entry (mappingOwner sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨value, size, guard, out, stor, logs⟩ :=
    singleMapping_pc0_inv s fork selector (lift_sound cert_check codeEq fork run)
  refine ⟨value, size, guard, ?_, stor, logs⟩
  rw [s.source_value slots, out]

theorem singleMapping_bytecode_live {sevm : Sevm} {b : Devm} {G c : Nat} {st : State}
    (s : SingleMappingGetter) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (s.slot sevm)) (slots : s.SlotMatches st sevm b) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty
      (G + c + 193 + s.storageGetter.dispatchGas)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st (s.entry (mappingOwner sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  refine ⟨_, lift_exact cert_check jumps_ok codeEq fork
    (singleMapping_pc0_exact s fork value size selector guard cost), ?_⟩
  obtain ⟨out, stor, logs, gas⟩ := getterWordPost_facts
    (b := afterSload sevm b (s.slot sevm)) (R := [0x039b, s.selector])
    (M := s.memory getterInitMemory (mappingOwner sevm).toB256)
    (v := b.getStorVal sevm.currentTarget (s.slot sevm)) (G := G)
    (s.memory_ptr getterInitMemory_ptr (mappingOwner sevm).toB256).wf
  refine ⟨gas, ?_, fun a => (stor a).trans (afterSload_getStor _ _ _ _),
    logs.trans (afterSload_logs _ _ _)⟩
  rw [s.source_value slots, out]

/-- The actual address decoder masks arbitrary high bits and permits arbitrary trailing bytes. -/
theorem balanceOf_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x70a08231)
    (slot : st.balanceOf (mappingOwner sevm) =
      b.getStorVal sevm.currentTarget (mapSlot (mappingOwner sevm).toB256 1))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      some post.output = getterResult st (.balanceOf (mappingOwner sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs :=
  singleMapping_bytecode_refines .balanceOf codeEq fork selector slot run

/-- Closed opcode overhead 380 plus the selected actual SLOAD charge, on both static settings. -/
theorem balanceOf_bytecode_live {sevm : Sevm} {b : Devm} {G c : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x70a08231)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (mapSlot (mappingOwner sevm).toB256 1))
    (slot : st.balanceOf (mappingOwner sevm) =
      b.getStorVal sevm.currentTarget (mapSlot (mappingOwner sevm).toB256 1)) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 380)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st (.balanceOf (mappingOwner sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [SingleMappingGetter.storageGetter, StorageGetter.dispatchGas,
    SingleMappingGetter.entry, Nat.add_assoc, Nat.reduceAdd] using
    (singleMapping_bytecode_live (G := G) .balanceOf codeEq fork value size selector guard cost slot)

/-- Pc-zero successful refinement uses the actual masked address and concrete mapping base 4. -/
theorem nonces_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x7ecebe00)
    (slot : st.nonces (mappingOwner sevm) =
      b.getStorVal sevm.currentTarget (mapSlot (mappingOwner sevm).toB256 4))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      some post.output = getterResult st (.nonces (mappingOwner sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs :=
  singleMapping_bytecode_refines .nonces codeEq fork selector slot run

/-- Closed opcode overhead 357 plus the selected actual SLOAD charge. -/
theorem nonces_bytecode_live {sevm : Sevm} {b : Devm} {G c : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x7ecebe00)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (mapSlot (mappingOwner sevm).toB256 4))
    (slot : st.nonces (mappingOwner sevm) =
      b.getStorVal sevm.currentTarget (mapSlot (mappingOwner sevm).toB256 4)) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 357)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st (.nonces (mappingOwner sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [SingleMappingGetter.storageGetter, StorageGetter.dispatchGas,
    SingleMappingGetter.entry, Nat.add_assoc, Nat.reduceAdd] using
    (singleMapping_bytecode_live (G := G) .nonces codeEq fork value size selector guard cost slot)

theorem allowance_pc0_exact {sevm : Sevm} {b : Devm} {G c : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xdd62ed3e)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (allowanceSlot sevm)) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + c + 493))
      (getterWordPost (afterSload sevm b (allowanceSlot sevm)) [0x039b, 0xdd62ed3e]
        (allowanceScratch2 getterInitMemory (mappingOwner sevm).toB256 (mappingSpender sevm).toB256)
        (b.getStorVal sevm.currentTarget (allowanceSlot sevm)) G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have gas : G + c + 493 = (G + c + 286) + 207 := by omega
  rw [gas]
  exact getterStorage_dispatch_exact .allowance value size selector
    (allowance_entry_exact fork getterInitMemory_ptr guard cost)

theorem allowance_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xdd62ed3e)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      post.output = (b.getStorVal sevm.currentTarget (allowanceSlot sevm)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := getterStorage_selector_inv .allowance selector run
  obtain ⟨guard, d, eq, out, stor, logs⟩ := allowance_entry_inv fork getterInitMemory_ptr run
  cases eq
  exact ⟨value, size, guard, out, stor, logs⟩

/-- Exact actual nested mapping order, with no hash injectivity premise. -/
theorem allowance_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xdd62ed3e)
    (slot : st.allowance (mappingOwner sevm) (mappingSpender sevm) =
      b.getStorVal sevm.currentTarget (allowanceSlot sevm))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      some post.output = getterResult st (.allowance (mappingOwner sevm) (mappingSpender sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨value, size, guard, out, stor, logs⟩ :=
    allowance_pc0_inv fork selector (lift_sound cert_check codeEq fork run)
  refine ⟨value, size, guard, ?_, stor, logs⟩
  simp only [getterResult, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, slot, out]

/-- Closed opcode overhead 493, including both KECCAK256 stages, plus the actual SLOAD charge. -/
theorem allowance_bytecode_live {sevm : Sevm} {b : Devm} {G c : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xdd62ed3e)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (cost : c = sloadCost sevm b (allowanceSlot sevm))
    (slot : st.allowance (mappingOwner sevm) (mappingSpender sevm) =
      b.getStorVal sevm.currentTarget (allowanceSlot sevm)) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 493)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st (.allowance (mappingOwner sevm) (mappingSpender sevm)) ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  refine ⟨_, lift_exact cert_check jumps_ok codeEq fork
    (allowance_pc0_exact fork value size selector guard cost), ?_⟩
  obtain ⟨out, stor, logs, gas⟩ := getterWordPost_facts
    (b := afterSload sevm b (allowanceSlot sevm)) (R := [0x039b, 0xdd62ed3e])
    (M := allowanceScratch2 getterInitMemory (mappingOwner sevm).toB256 (mappingSpender sevm).toB256)
    (v := b.getStorVal sevm.currentTarget (allowanceSlot sevm)) (G := G)
    (allowanceScratch2_ptr getterInitMemory_ptr (mappingOwner sevm).toB256 (mappingSpender sevm).toB256).wf
  refine ⟨gas, ?_, fun a => (stor a).trans (afterSload_getStor _ _ _ _),
    logs.trans (afterSload_logs _ _ _)⟩
  simp only [getterResult, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, slot, out]

end Blanc.Lift.UniswapV2Pair
