import Blanc.Lift.UniswapV2Pair.GetterStorageReservesWrapper

/-! Successful pc-zero source refinement and exact-gas liveness for getReserves. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem reserves_pc0_exact {sevm : Sevm} {b : Devm} {G c : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x0902f1ac)
    (cost : c = sloadCost sevm b 8) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + c + 404))
      (getterReservesPost (afterSload sevm b 8) [0x0902f1ac] getterInitMemory
        (reserve0Read (b.getStorVal sevm.currentTarget 8))
        (reserve1Read (b.getStorVal sevm.currentTarget 8))
        (reserveTimestampRead (b.getStorVal sevm.currentTarget 8)) G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have body := reserves_entry_exact (G := G) (sel := 0x0902f1ac) fork cost getterInitMemory_ptr
  simpa only [StorageGetter.dispatchGas, StorageGetter.selector, StorageGetter.entryTree,
    Nat.add_assoc, Nat.reduceAdd] using getterStorage_dispatch_exact .getReserves value size selector body

theorem reserves_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x0902f1ac)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      post.output = encodeWords
        [reserve0Read (b.getStorVal sevm.currentTarget 8),
         reserve1Read (b.getStorVal sevm.currentTarget 8),
         reserveTimestampRead (b.getStorVal sevm.currentTarget 8)] ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := getterStorage_selector_inv .getReserves selector run
  obtain ⟨d, eq, out, stor, logs⟩ := reserves_entry_inv fork getterInitMemory_ptr run
  cases eq
  exact ⟨value, size, out, stor, logs⟩

theorem getReserves_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x0902f1ac)
    (slots : ReserveSlotMatches st sevm b)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .getReserves ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨value, size, out, stor, logs⟩ :=
    reserves_pc0_inv fork selector (lift_sound cert_check codeEq fork run)
  refine ⟨value, size, ?_, stor, logs⟩
  rw [reserveSource_result slots, out]

theorem getReserves_bytecode_live {sevm : Sevm} {b : Devm} {G c : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x0902f1ac)
    (cost : c = sloadCost sevm b 8) (slots : ReserveSlotMatches st sevm b) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 404)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .getReserves ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  refine ⟨_, lift_exact cert_check jumps_ok codeEq fork
    (reserves_pc0_exact fork value size selector cost), ?_⟩
  obtain ⟨out, stor, logs, gas⟩ := getterReservesPost_facts
    (b := afterSload sevm b 8) (R := [0x0902f1ac]) (G := G)
    (r0 := reserve0Read (b.getStorVal sevm.currentTarget 8))
    (r1 := reserve1Read (b.getStorVal sevm.currentTarget 8))
    (ts := reserveTimestampRead (b.getStorVal sevm.currentTarget 8)) getterInitMemory_ptr
  refine ⟨gas, ?_, fun a => (stor a).trans (afterSload_getStor _ _ _ _),
    logs.trans (afterSload_logs _ _ _)⟩
  rw [reserveSource_result slots, out]

end Blanc.Lift.UniswapV2Pair
