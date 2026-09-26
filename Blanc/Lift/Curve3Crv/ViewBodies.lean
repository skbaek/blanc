import Blanc.Lift.Curve3Crv.Spec

/-!
# The word views' bodies, forward with exact gas

`totalSupply()`, `decimals()`, `balanceOf(a)` and `allowance(o, p)` from the body's entry state
(`entrySt`: the prologue's memory, empty stack) to `RETURN`, in the segment interface
`BodyLive`: `SLOAD` (warm or cold, `sloadCost`) of the slot, `mstore(0, word)`,
`return(0, 32)`.  Memory never grows past `0x100` (`0xc0` + the mapping scratch words).
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

section

variable {sevm : Sevm} {b : Devm}

/-- A frame word read back from the prologue's image. -/
private theorem vyMem_size (w : B256) : (vyMem Mem.empty w).size = 192 := vyMem_empty_size w

/-- The tail every word view ends with: `SLOAD` the key on the stack, return the word. -/
private theorem word_tail (hfork : CoveredFork sevm.benvStat.fork) {M : Mem} {img : Bytes}
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hn : 32 ≤ M.size) (hn32 : M.size % 32 = 0)
    (k : B256) (G : Nat) :
    ∃ post, SFunc.RunExact prog sevm (St b [k] M (G + 3 + 3 + 3 + 3 + sloadCost sevm b k))
      (.next (.reg .sload) (.next (.push [0x00] (by decide)) (.next (.reg .mstore)
        (.next (.push [0x20] (by decide)) (.next (.push [0x00] (by decide)) (.last .return_))))))
      (.halted post) ∧ post.gasLeft = G ∧
      Lands sevm b post (Devm.getStor b sevm.currentTarget, [],
        some (b.getStorVal sevm.currentTarget k).toBytes) := by
  have hsz : (M.write 0 (b.getStorVal sevm.currentTarget k).toBytes).size = M.size :=
    Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)
  have h0 : (0 : B256).toNat = 0 := by decide
  have h32 : (32 : B256).toNat = 32 := by decide
  have hread : ((M.write 0 (b.getStorVal sevm.currentTarget k).toBytes).read
      (0 : B256).toNat (32 : B256).toNat).1 = (b.getStorVal sevm.currentTarget k).toBytes := by
    rw [Mem.Reads.read (hr.write hwf 0 _)]
    exact sliceD_word_same _ _ _
  refine ⟨((St (afterSload sevm b k) [] (M.write 0 (b.getStorVal sevm.currentTarget k).toBytes)
    G).memRead 0 32).2.withOutput (b.getStorVal sevm.currentTarget k).toBytes,
    rx_sload_sel hfork (by simp) ?_, rfl, ?_⟩
  · refine rx_push (w := 0) rfl (by simp) ?_
    refine rx_mstore (c := 3) ?_ rfl ?_
    · rw [h0, St, Devm.extCost_zero_of_le hn32 (by omega)]; rfl
    refine rx_push (w := 32) rfl (by simp) ?_
    refine rx_push (w := 0) rfl (by simp) ?_
    refine rx_return ?_ hread
    rw [h0, h32, St, Devm.extCost_zero_of_le (by rw [hsz]; exact hn32) (by rw [hsz]; omega)]
  · refine ⟨?_, fun a _ => ?_, ?_, fun o ho => ?_⟩
    · show Devm.getStor (afterSload sevm b k) _ = _
      rw [afterSload_getStor]
    · show Devm.getStor (afterSload sevm b k) _ = _
      rw [afterSload_getStor]
    · show (afterSload sevm b k).logs = _
      rw [afterSload_logs, List.append_nil]
    · cases ho
      rfl

private theorem entry_wf (sevm : Sevm) : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) :=
  vyMem_wf Mem.wf_empty _

private theorem entry_reads (sevm : Sevm) :
    Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0)) (vyImg [] (Sevm.dataWord sevm 0)) :=
  vyMem_reads Mem.wf_empty Mem.reads_empty _

/-- `totalSupply()`: 34 gas and the `SLOAD` of slot 5. -/
theorem live_totalSupply (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawTotalSupply sevm (Devm.getStor b sevm.currentTarget) = some r) :
    BodyLive sevm b t_0240_c0 r := by
  unfold rawTotalSupply at hr
  split_ifs at hr with hv
  cases hr
  refine ⟨34 + sloadCost sevm b vySupplySlot, fun G _ => ?_⟩
  obtain ⟨post, hrun, hg, hl⟩ := word_tail (b := b) hfork (entry_wf sevm) (entry_reads sevm)
    (by rw [vyMem_size]; omega) (by rw [vyMem_size]) vySupplySlot G
  refine ⟨post, ?_, hg, hl⟩
  unfold entrySt t_0240_c0
  rw [show G + (34 + sloadCost sevm b vySupplySlot) =
    G + 3 + 3 + 3 + 3 + sloadCost sevm b vySupplySlot + 3 + 1 + 10 + 3 + 3 + 2 by omega]
  refine rx_callvalue (by simp) ?_
  rw [hv]
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_024a_c0
  refine rx_dest ?_
  refine rx_push (w := vySupplySlot) rfl (by simp) ?_
  exact hrun

/-- `decimals()`: 34 gas and the `SLOAD` of slot 2. -/
theorem live_decimals (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawDecimals sevm (Devm.getStor b sevm.currentTarget) = some r) :
    BodyLive sevm b t_087e_c0 r := by
  unfold rawDecimals at hr
  split_ifs at hr with hv
  cases hr
  refine ⟨34 + sloadCost sevm b vyDecimalsSlot, fun G _ => ?_⟩
  obtain ⟨post, hrun, hg, hl⟩ := word_tail (b := b) hfork (entry_wf sevm) (entry_reads sevm)
    (by rw [vyMem_size]; omega) (by rw [vyMem_size]) vyDecimalsSlot G
  refine ⟨post, ?_, hg, hl⟩
  unfold entrySt
  rw [show G + (34 + sloadCost sevm b vyDecimalsSlot) =
    G + 3 + 3 + 3 + 3 + sloadCost sevm b vyDecimalsSlot + 3 + 19 by omega]
  refine rx_vyNonpayable (h := 0x08) (l := 0x88) (fail := t_0884_c0) hv (by simp) ?_
  refine rx_push (w := vyDecimalsSlot) rfl (by simp) ?_
  exact hrun

/-- The mapping-slot scratch sequence of a view, forward: `PUSH1 slot`, the key word, then
`mstore(0xe0, key); mstore(0xc0, slot); keccak(0xc0, 0x40)` over a memory of at most eight words
(`c1` the first store's charge: 9 when memory grows from six words, 3 from eight). -/
private theorem slot_seq {M : Mem} {n c1 : Nat} (hM : M.size = n) (hn : n ≤ 256)
    (hc1 : gVerylow + (calculateMemoryGasCost (memExtSize n 224 32) - calculateMemoryGasCost n)
      = c1) (slot key : B256) {f : SFunc} {o : Outcome} (G : Nat)
    (k : SFunc.RunExact prog sevm
      (St b [mapSlot slot key] ((M.write 224 key.toBytes).write 192 slot.toBytes) G) f o) :
    SFunc.RunExact prog sevm (St b [key, slot] M (G + 42 + 3 + 3 + 3 + 3 + c1 + 3))
      (.next (.push [0xe0] (by decide)) (.next (.reg .mstore) (.next (.push [0xc0] (by decide))
        (.next (.reg .mstore) (.next (.push [0x40] (by decide)) (.next (.push [0xc0] (by decide))
          (.next (.reg .keccak256) f))))))) o := by
  have he0 : (Bytes.toB256 [0xe0]).toNat = 224 := by decide
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 192 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hs1 : (M.write 224 key.toBytes).size = 256 := by
    rw [Mem.size_write_word_at, hM]
    split_ifs with h
    · omega
    · rfl
  have hs2 : ((M.write 224 key.toBytes).write 192 slot.toBytes).size = 256 := by
    rw [Mem.size_write_word_at, hs1]; rfl
  refine rx_push rfl (by simp) ?_
  refine rx_mstore (c := c1) ?_ (M' := M.write 224 key.toBytes) (by rw [he0]) ?_
  · rw [he0, St.extCost_eq hM]; exact hc1
  refine rx_push rfl (by simp) ?_
  refine rx_mstore (c := 3) ?_ (M' := (M.write 224 key.toBytes).write 192 slot.toBytes)
    (by rw [hc0]) ?_
  · rw [hc0, St, Devm.extCost_zero_of_le (by rw [hs1]) (by rw [hs1]; omega)]; rfl
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_keccak (c := 42) ?_ ?_ ?_ (by simp) k
  · rw [hc0, h40, St, Devm.extCost_zero_of_le (by rw [hs2]) (by rw [hs2])]; decide
  · rw [hc0, h40]; exact vySlot_keccak M slot key
  · rw [hc0, h40]
    exact Mem.read_snd_eq_self (by rw [hs2]; rfl)

/-- `balanceOf(a)`: the non-payable guard, the address clamp, the slot `keccak(3 ‖ a)`, 140 gas
and its `SLOAD`. -/
theorem live_balanceOf (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawBalanceOf sevm (Devm.getStor b sevm.currentTarget) = some r) :
    BodyLive sevm b t_08a5_c0 r := by
  unfold rawBalanceOf at hr
  split_ifs at hr with hguard
  obtain ⟨hv, ha⟩ := hguard
  cases hr
  set a := Sevm.argWord sevm 0
  have ha4 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = a := rfl
  refine ⟨140 + sloadCost sevm b (mapSlot 3 a), fun G _ => ?_⟩
  have hM := vyMem_size (Sevm.dataWord sevm 0)
  set M := vyMem Mem.empty (Sevm.dataWord sevm 0)
  obtain ⟨post, hrun, hg, hl⟩ := word_tail (b := b)
    (M := (M.write 224 a.toBytes).write 192 (3 : B256).toBytes) hfork
    (((entry_wf sevm).write _ _).write _ _) (((entry_reads sevm).write (entry_wf sevm) _ _).write
      ((entry_wf sevm).write _ _) _ _)
    (by rw [Mem.size_write_word_at, Mem.size_write_word_at, hM]; decide)
    (by rw [Mem.size_write_word_at, Mem.size_write_word_at, hM]; decide) (mapSlot 3 a) G
  refine ⟨post, ?_, hg, hl⟩
  unfold entrySt
  rw [show G + (140 + sloadCost sevm b (mapSlot 3 a)) =
    G + 3 + 3 + 3 + 3 + sloadCost sevm b (mapSlot 3 a) + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3
      + 34 + 19 by omega]
  refine rx_vyNonpayable (h := 0x08) (l := 0xaf) (fail := t_08ab_c0) hv (by simp) ?_
  refine rx_vyAddrArg (p := 0x04) (h := 0x08) (l := 0xc0) (fail := t_08bc_c0) (entry_reads sevm)
    (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega) (by rw [ha4]; exact ha) (by simp) ?_
  refine rx_push (w := 3) rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [ha4]
  exact slot_seq (c1 := 9) hM (by omega) (by decide) 3 a _ hrun

/-- `allowance(o, p)`: the guard, two clamps, the nested slot `keccak(keccak(4 ‖ o) ‖ p)`, 240 gas
and its `SLOAD`. -/
theorem live_allowance (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawAllowance sevm (Devm.getStor b sevm.currentTarget) = some r) :
    BodyLive sevm b t_0267_c0 r := by
  unfold rawAllowance at hr
  split_ifs at hr with hguard
  obtain ⟨hv, ho, hp⟩ := hguard
  cases hr
  set o := Sevm.argWord sevm 0
  set q := Sevm.argWord sevm 1
  have ho4 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = o := rfl
  have hq4 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = q := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  set k := mapSlot (mapSlot 4 o) q
  refine ⟨240 + sloadCost sevm b k, fun G _ => ?_⟩
  have hM := vyMem_size (Sevm.dataWord sevm 0)
  set M := vyMem Mem.empty (Sevm.dataWord sevm 0)
  set M1 := (M.write 224 o.toBytes).write 192 (4 : B256).toBytes
  have hs1 : M1.size = 256 := by
    simp only [M1, Mem.size_write_word_at, hM]; decide
  have hwf1 : Mem.Wf M1 := ((entry_wf sevm).write _ _).write _ _
  have hr1 : Mem.Reads M1 (Bytes.writeAt (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 224
      o.toBytes) 192 (4 : B256).toBytes) := ((entry_reads sevm).write (entry_wf sevm) _ _).write ((entry_wf sevm).write _ _) _ _
  obtain ⟨post, hrun, hg, hl⟩ := word_tail (b := b)
    (M := (M1.write 224 q.toBytes).write 192 (mapSlot 4 o).toBytes) hfork
    ((hwf1.write _ _).write _ _) ((hr1.write hwf1 _ _).write (hwf1.write _ _) _ _)
    (by rw [Mem.size_write_word_at, Mem.size_write_word_at, hs1]; decide)
    (by rw [Mem.size_write_word_at, Mem.size_write_word_at, hs1]; decide) k G
  refine ⟨post, ?_, hg, hl⟩
  unfold entrySt
  rw [show G + (240 + sloadCost sevm b k) =
    G + 3 + 3 + 3 + 3 + sloadCost sevm b k + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3
      + 3 + 9 + 3 + 3 + 3 + 3 + 34 + 34 + 19 by omega]
  refine rx_vyNonpayable (h := 0x02) (l := 0x71) (fail := t_026d_c0) hv (by simp) ?_
  refine rx_vyAddrArg (p := 0x04) (h := 0x02) (l := 0x82) (fail := t_027e_c0) (entry_reads sevm)
    (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega) (by rw [ho4]; exact ho) (by simp) ?_
  refine rx_vyAddrArg (p := 0x24) (h := 0x02) (l := 0x94) (fail := t_0290_c0) (entry_reads sevm)
    (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega) (by rw [hq4]; exact hp) (by simp) ?_
  refine rx_push (w := 4) rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [ho4]
  refine slot_seq (c1 := 9) hM (by omega) (by decide) 4 o _ ?_
  refine rx_push rfl (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [hq4]
  exact slot_seq (c1 := 3) hs1 (by omega) (by decide) (mapSlot 4 o) q _ hrun

end

end Blanc.Lift.Curve3Crv
