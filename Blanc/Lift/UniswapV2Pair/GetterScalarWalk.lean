import Blanc.Lift.UniswapV2Pair.GetterScalarWrapper
import Blanc.Lift.UniswapV2Pair.GetterScalarDispatch

/-! Actual pc-zero source refinement and exact-gas liveness for ten scalar getters. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem getterScalar_pc0_exact {sevm : Sevm} {b : Devm} {G : Nat}
    (s : ScalarGetter) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector) :
    SProg.RunExact cert.prog sevm
      (St b [] Mem.empty (G + s.loadGas sevm b + s.entryGas + s.dispatchGas))
      (getterWordPost (s.after sevm b) [s.tag, s.selector]
        getterInitMemory (s.value sevm b) G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  exact getterScalar_dispatch_exact s value size selector
    (getterScalar_entry_exact s fork rfl getterInitMemory_ptr)

theorem getterScalar_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (s : ScalarGetter) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      post.output = (s.value sevm b).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := getterScalar_selector_inv s selector run
  obtain ⟨d, eq, out, stor, logs⟩ := getterScalar_entry_inv s fork getterInitMemory_ptr run
  cases eq
  exact ⟨value, size, out, stor, logs⟩

theorem getterScalar_bytecode_exact {sevm : Sevm} {b : Devm} {G : Nat}
    (s : ScalarGetter) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector) :
    Nonempty (Exec 0 sevm
      (St b [] Mem.empty (G + s.loadGas sevm b + s.entryGas + s.dispatchGas))
      (.ok (getterWordPost (s.after sevm b) [s.tag, s.selector]
        getterInitMemory (s.value sevm b) G))) :=
  lift_exact cert_check jumps_ok codeEq fork (getterScalar_pc0_exact s fork value size selector)

theorem getterScalar_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (s : ScalarGetter) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (slots : s.SlotMatches st sevm b)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st s.entry ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨value, size, out, stor, logs⟩ :=
    getterScalar_pc0_inv s fork selector (lift_sound cert_check codeEq fork run)
  refine ⟨value, size, ?_, stor, logs⟩
  rw [s.source_value slots, out]

theorem getterScalar_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (s : ScalarGetter) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector) (slots : s.SlotMatches st sevm b) :
    ∃ post, Nonempty (Exec 0 sevm
      (St b [] Mem.empty (G + s.loadGas sevm b + s.entryGas + s.dispatchGas)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st s.entry ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  refine ⟨_, getterScalar_bytecode_exact s codeEq fork value size selector, ?_⟩
  obtain ⟨out, stor, logs, gas⟩ := getterWordPost_facts
    (b := s.after sevm b) (R := [s.tag, s.selector]) (v := s.value sevm b) (G := G)
    getterInitMemory_ptr.wf
  refine ⟨gas, ?_, fun a => (stor a).trans (s.after_storage sevm b a),
    logs.trans (s.after_logs sevm b)⟩
  rw [s.source_value slots, out]

/-- Successful execution at pc zero refines the source decimals getter. -/
theorem decimals_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x313ce567)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .decimals ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.constant .decimals) codeEq fork selector True.intro run

/-- Source-result liveness with exact opcode overhead 297. -/
theorem decimals_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x313ce567)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + 297)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .decimals ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using
    (getterScalar_bytecode_live (G := G) (.constant .decimals) codeEq fork value size selector True.intro)

/-- Successful execution at pc zero refines the source minimumLiquidity getter. -/
theorem minimumLiquidity_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xba9a7a56)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .minimumLiquidity ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.constant .minimumLiquidity) codeEq fork selector True.intro run

/-- Source-result liveness with exact opcode overhead 243. -/
theorem minimumLiquidity_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xba9a7a56)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + 243)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .minimumLiquidity ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using
    (getterScalar_bytecode_live (G := G) (.constant .minimumLiquidity) codeEq fork value size selector True.intro)

/-- Successful execution at pc zero refines the source permitTypehash getter. -/
theorem permitTypehash_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x30adf81f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .permitTypehash ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.constant .permitTypehash) codeEq fork selector True.intro run

/-- Source-result liveness with exact opcode overhead 266. -/
theorem permitTypehash_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x30adf81f)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + 266)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .permitTypehash ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using
    (getterScalar_bytecode_live (G := G) (.constant .permitTypehash) codeEq fork value size selector True.intro)

/-- Successful execution at pc zero refines the source domainSeparator getter. -/
theorem domainSeparator_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x3644e515)
    (slots : st.domainSeparator = b.getStorVal sevm.currentTarget 3)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .domainSeparator ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.stored .domainSeparator) codeEq fork selector slots run

/-- Source-result liveness with exact opcode overhead 243 and the actual selected SLOAD charge. -/
theorem domainSeparator_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x3644e515)
    (slots : st.domainSeparator = b.getStorVal sevm.currentTarget 3)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + sloadCost sevm b 3 + 243)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .domainSeparator ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, StoredScalar.slot, StoredScalar.slotByte, show Bytes.toB256 [0x3] = (3 : B256) from rfl] using
    (getterScalar_bytecode_live (G := G) (.stored .domainSeparator) codeEq fork value size selector slots)

/-- Successful execution at pc zero refines the source price0CumulativeLast getter. -/
theorem price0CumulativeLast_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x5909c0d5)
    (slots : st.price0CumulativeLast = b.getStorVal sevm.currentTarget 9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .price0CumulativeLast ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.stored .price0CumulativeLast) codeEq fork selector slots run

/-- Source-result liveness with exact opcode overhead 287 and the actual selected SLOAD charge. -/
theorem price0CumulativeLast_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x5909c0d5)
    (slots : st.price0CumulativeLast = b.getStorVal sevm.currentTarget 9)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + sloadCost sevm b 9 + 287)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .price0CumulativeLast ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, StoredScalar.slot, StoredScalar.slotByte, show Bytes.toB256 [0x9] = (9 : B256) from rfl] using
    (getterScalar_bytecode_live (G := G) (.stored .price0CumulativeLast) codeEq fork value size selector slots)

/-- Successful execution at pc zero refines the source price1CumulativeLast getter. -/
theorem price1CumulativeLast_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x5a3d5493)
    (slots : st.price1CumulativeLast = b.getStorVal sevm.currentTarget 10)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .price1CumulativeLast ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.stored .price1CumulativeLast) codeEq fork selector slots run

/-- Source-result liveness with exact opcode overhead 309 and the actual selected SLOAD charge. -/
theorem price1CumulativeLast_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x5a3d5493)
    (slots : st.price1CumulativeLast = b.getStorVal sevm.currentTarget 10)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + sloadCost sevm b 10 + 309)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .price1CumulativeLast ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, StoredScalar.slot, StoredScalar.slotByte, show Bytes.toB256 [0xa] = (10 : B256) from rfl] using
    (getterScalar_bytecode_live (G := G) (.stored .price1CumulativeLast) codeEq fork value size selector slots)

/-- Successful execution at pc zero refines the source kLast getter. -/
theorem kLast_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x7464fc3d)
    (slots : st.kLast = b.getStorVal sevm.currentTarget 11)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .kLast ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.stored .kLast) codeEq fork selector slots run

/-- Source-result liveness with exact opcode overhead 288 and the actual selected SLOAD charge. -/
theorem kLast_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x7464fc3d)
    (slots : st.kLast = b.getStorVal sevm.currentTarget 11)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + sloadCost sevm b 11 + 288)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .kLast ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, StoredScalar.slot, StoredScalar.slotByte, show Bytes.toB256 [0xb] = (11 : B256) from rfl] using
    (getterScalar_bytecode_live (G := G) (.stored .kLast) codeEq fork value size selector slots)

/-- Successful execution at pc zero refines the source factory getter. -/
theorem factory_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xc45a0155)
    (slots : st.factory = (b.getStorVal sevm.currentTarget 5).toAdr)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .factory ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.address .factory) codeEq fork selector slots run

/-- Source-result liveness with exact opcode overhead 302 and the actual selected SLOAD charge. -/
theorem factory_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xc45a0155)
    (slots : st.factory = (b.getStorVal sevm.currentTarget 5).toAdr)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + sloadCost sevm b 5 + 302)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .factory ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, AddressScalar.slot, AddressScalar.slotByte, show Bytes.toB256 [0x5] = (5 : B256) from rfl] using
    (getterScalar_bytecode_live (G := G) (.address .factory) codeEq fork value size selector slots)

/-- Successful execution at pc zero refines the source token0 getter. -/
theorem token0_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xdfe1681)
    (slots : st.token0 = (b.getStorVal sevm.currentTarget 6).toAdr)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .token0 ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.address .token0) codeEq fork selector slots run

/-- Source-result liveness with exact opcode overhead 281 and the actual selected SLOAD charge. -/
theorem token0_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xdfe1681)
    (slots : st.token0 = (b.getStorVal sevm.currentTarget 6).toAdr)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + sloadCost sevm b 6 + 281)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .token0 ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, AddressScalar.slot, AddressScalar.slotByte, show Bytes.toB256 [0x6] = (6 : B256) from rfl] using
    (getterScalar_bytecode_live (G := G) (.address .token0) codeEq fork value size selector slots)

/-- Successful execution at pc zero refines the source token1 getter. -/
theorem token1_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd21220a7)
    (slots : st.token1 = (b.getStorVal sevm.currentTarget 7).toAdr)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .token1 ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  exact getterScalar_bytecode_refines (.address .token1) codeEq fork selector slots run

/-- Source-result liveness with exact opcode overhead 257 and the actual selected SLOAD charge. -/
theorem token1_bytecode_live {sevm : Sevm} {b : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xd21220a7)
    (slots : st.token1 = (b.getStorVal sevm.currentTarget 7).toAdr)
    : ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + sloadCost sevm b 7 + 257)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .token1 ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  simpa only [ScalarGetter.entry, ScalarGetter.loadGas, ScalarGetter.entryGas, ScalarGetter.calleeGas, ScalarGetter.tailGas, ScalarGetter.dispatchGas, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, AddressScalar.slot, AddressScalar.slotByte, show Bytes.toB256 [0x7] = (7 : B256) from rfl] using
    (getterScalar_bytecode_live (G := G) (.address .token1) codeEq fork value size selector slots)

end Blanc.Lift.UniswapV2Pair
