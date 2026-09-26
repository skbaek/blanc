import Blanc.Lift.Curve3Crv.ViewBodies
import Blanc.Lift.Curve3Crv.Refine
import Blanc.Lift.StaticCall

/-!
# Liveness: the bodies, forward with exact gas

Each segment builds a gas-exact run of one function body inside entry 0 from its entry state
(`BodyLive`), for a raw effect that succeeds: the converse of the matching `SafeBodies`
segment, with the same walk read forwards (`rx_vyNonpayable`, `rx_vyAddrArg`, `rx_caller`,
`rx_keccak` with `vySlot_keccak`, `rx_sload_sel`, `rx_sstore` at its selected cost, `rx_log3`,
`rx_return`).  The word views are proved in `ViewBodies.lean`; `live_at` assembles all bodies
but `set_name`, whose call to an unknown contract makes its gas inexact (`live_setName`).
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

section

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

-- SEGMENT: liveSetMinter (36 nodes)
/-- `set_minter`.  Proof sketch: `rx_vyNonpayable`, `rx_vyAddrArg`, `rx_push`, `rx_sload_sel`,
`rx_caller`, `rx_eq (v := 1)`, `rx_push`, `rx_branch_succ`, `rx_dest`, `rx_push`,
`rx_calldataload`, `rx_push`, `rx_sstore` (sentry: `gCallStipend < G` suffices, the charge
after the `SSTORE` is 0), `.last` of `STOP`.  Cost:
`19 + 34 + 3 + sloadCost + 2 + 3 + 3 + 10 + 1 + 3 + 3 + 3 + sstoreCost`. -/
theorem live_setMinter (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawSetMinter sevm stor₀ = some r) : BodyLive sevm b t_00b0_c0 r := by
  unfold rawSetMinter at hr
  split_ifs at hr with hg
  obtain ⟨hv, hm, hmin⟩ := hg
  cases hr
  set m := Sevm.argWord sevm 0
  set b1 := afterSload sevm b vyMinterSlot
  have hm4 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = m := rfl
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  refine ⟨sstoreCost sevm b1 vyMinterSlot m + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 +
    sloadCost sevm b vyMinterSlot + 3 + 34 + 19, fun G hG => ?_⟩
  refine ⟨St (afterSstore sevm b1 vyMinterSlot m) [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G,
    ?_, rfl, ?_⟩
  · unfold entrySt
    rw [show G + (sstoreCost sevm b1 vyMinterSlot m + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 +
      sloadCost sevm b vyMinterSlot + 3 + 34 + 19) = G + sstoreCost sevm b1 vyMinterSlot m + 3 + 3
      + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x00) (l := 0xba) (fail := t_00b6_c0) hv (by simp) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x00) (l := 0xcb) (fail := t_00c7_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hm4]; exact hm) (by simp) ?_
    refine rx_push (w := vyMinterSlot) rfl (by simp) ?_
    refine rx_sload_sel hfork (by simp) ?_
    refine rx_caller (by simp) ?_
    refine rx_eq (v := 1) ?_ (by simp) ?_
    · have : b.getStorVal sevm.currentTarget vyMinterSlot = sevm.caller.toB256 := hmin
      simp [B256.eqCheck, this]
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) ?_
    refine rx_dest ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hm4]
    refine rx_push (w := vyMinterSlot) rfl (by simp) ?_
    refine rx_sstore hfork (by omega) hstatic ?_
    exact .last rfl
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => by cases ho⟩
    · show Devm.getStor (afterSstore sevm b1 vyMinterSlot m) _ = _
      rw [afterSstore_getStor_self, afterSload_getStor]
    · show Devm.getStor (afterSstore sevm b1 vyMinterSlot m) _ = _
      rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]
    · show (afterSstore sevm b1 vyMinterSlot m).logs = _
      rw [afterSstore_logs, afterSload_logs, List.append_nil]

-- SEGMENT: liveTransfer (107 nodes)
/-- `transfer`.  Proof sketch: the walk of `safeTransfer` forwards; the two slots by the
scratch sequence (`slot_seq`-style helper as in `ViewBodies.lean`, generalised to a stack
tail), the guards' flags from `rawTransfer`'s conditions, the `SSTORE`s at `sstoreCost` over
the evolving base (`afterSload`, `afterSstore`), `rx_log3` (static frame excluded by
`hstatic`), `rx_return` of `(1 : B256).toBytes`.  The cost is a sum of constants and the two
`sloadCost`/`sstoreCost` terms, all fixed by `b`. -/
theorem live_transfer (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawTransfer sevm stor₀ = some r) : BodyLive sevm b t_02ce_c0 r := by
  unfold rawTransfer at hr
  dsimp only at hr
  split_ifs at hr with hg
  obtain ⟨hv, hd, hle, hnof⟩ := hg
  cases hr
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have h3 : Bytes.toB256 [0x03] = 3 := by decide
  have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  set d := Sevm.argWord sevm 0
  set v := Sevm.argWord sevm 1
  set s1 := mapSlot 3 sevm.caller.toB256
  set s2 := mapSlot 3 d
  set x := b.getStorVal sevm.currentTarget s1
  set b2 := afterSstore sevm (afterSload sevm b s1) s1 (x - v)
  set y := b2.getStorVal sevm.currentTarget s2
  have hy : y = (((stor₀).set s1 ((stor₀).get s1 - v)).get s2) := getStorVal_afterStore
  set M1 := ((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 224 sevm.caller.toB256.toBytes).write
    192 (3 : B256).toBytes
  have hM1 : M1.size = 256 := by simp only [M1, Mem.size_write_word_at, hM]; decide
  set M2 := (M1.write 224 d.toBytes).write 192 (3 : B256).toBytes
  have hM2 : M2.size = 256 := by simp only [M2, Mem.size_write_word_at, hM1]; decide
  have hwf2 : Mem.Wf M2 := ((((hwf0.write _ _).write _ _).write _ _).write _ _)
  set M3 := M2.write 320 v.toBytes
  have hM3 : M3.size = 352 := by simp only [M3, Mem.size_write_word_at, hM2]; decide
  refine ⟨3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 34 + 19, fun G hG => ?_⟩
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  set b4 := (afterSstore sevm (afterSload sevm b2 s2) s2 (y + v)).addLog
    ⟨sevm.currentTarget, [transferTopic, sevm.caller.toB256, d], v.toBytes⟩
  set M5 := M3.write 0 (1 : B256).toBytes
  refine ⟨((St b4 [] M5 G).memRead 0 32).2.withOutput (1 : B256).toBytes, ?_, rfl, ?_⟩
  · unfold entrySt
    rw [show G + (3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 34 + 19) = G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x02) (l := 0xd8) (fail := t_02d4_c0) hv (by simp) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x02) (l := 0xe9) (fail := t_02e5_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hd0]; exact hd) (by simp) ?_
    refine rx_push (w := 3) h3 (by simp) ?_
    refine rx_caller (by simp) ?_
    refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_vySubStore (p := 0x24) (h := 0x03) (l := 0x0a) (fail := t_0306_c0) hfork hstatic
      (by rw [hv1]; exact hle) (by omega) (by simp) ?_
    rw [hv1]
    refine rx_push (w := 3) h3 (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_vySlot (c1 := 3) hM1 (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_vyAddStore (p := 0x24) (h := 0x03) (l := 0x38) (fail := t_0334_c0) hfork hstatic
      (by rw [hv1]; show y.toNat + v.toNat < 2 ^ 256; rw [hy]; exact hnof) (by omega) (by simp) ?_
    rw [hv1]
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hv1]
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 12) ?_ (M' := M3) (by rw [h320]) ?_
    · rw [h320, St.extCost_eq hM2]; decide
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_caller (by simp) ?_
    refine rx_push (w := transferTopic) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_log3 (c := 1756) (data := v.toBytes) hstatic ?_ ?_ ?_ ?_
    · rw [h320, h32, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3])]; decide
    · rw [h320, h32]; exact Mem.read_write_word_of_wf hwf2 320 v
    · rw [h320, h32]; exact read_covered hM3 (by decide) (by decide)
    refine rx_push (w := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 3) ?_ (M' := M5) (by rw [h0]) ?_
    · rw [h0, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3]; omega)]; rfl
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_return ?_ ?_
    · have hM5 : M5.size = 352 := by simp only [M5, Mem.size_write_word_at, hM3]; decide
      rw [h0, h32, St, Devm.extCost_zero_of_le (by rw [hM5]) (by rw [hM5]; omega)]
    · rw [h0, h32]; exact Mem.read_write_word_of_wf hwf3 0 1
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore, getStor_afterStore, hy]
      rfl
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha]
    · rw [logs_St_return, logs_addLog, logs_afterStore, logs_afterStore]
    · cases ho
      exact output_St_return _ _ _ _ _ _ _

-- SEGMENT: liveTransferFrom (172 nodes)
/-- `transferFrom`: forwards of `safeTransferFrom`, the minter branch decided by `rawTransferFrom`'s
`spend`: `rx_branchTo_succ` into entry 3 when the caller is the minter, the allowance block
otherwise; the shared tail proved once over an arbitrary base. -/
theorem live_transferFrom (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw} (hr : rawTransferFrom sevm stor₀ = some r) :
    BodyLive sevm b t_0390_c0 r := by
  sorry

-- SEGMENT: liveApprove (97 nodes)
/-- `approve`: forwards of `safeApprove`; the zero-value arm (`.jump 4`) or the read arm, joined
at entry 4. -/
theorem live_approve (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawApprove sevm stor₀ = some r) : BodyLive sevm b t_04ab_c0 r := by
  sorry

-- SEGMENT: liveMintBurn (121 + 117 nodes)
/-- `mint` and `burnFrom`: forwards of `safeMintBurn`. -/
theorem live_mint (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawMint sevm stor₀ = some r) : BodyLive sevm b t_056e_c0 r := by
  unfold rawMint at hr
  dsimp only at hr
  split_ifs at hr with hg
  obtain ⟨hv, hd, hmin, hnz, hsup, hbal⟩ := hg
  cases hr
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have h3 : Bytes.toB256 [0x03] = 3 := by decide
  have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  set d := Sevm.argWord sevm 0
  set v := Sevm.argWord sevm 1
  set s2 := mapSlot 3 d
  set b1 := afterSload sevm b vyMinterSlot
  set sup := b1.getStorVal sevm.currentTarget vySupplySlot
  have hsup' : sup = (stor₀).get vySupplySlot := getStorVal_afterSload
  set b2 := afterSstore sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v)
  set y := b2.getStorVal sevm.currentTarget s2
  have hy : y = (((stor₀).set vySupplySlot ((stor₀).get vySupplySlot + v)).get s2) := by
    show b2.getStorVal _ _ = _
    rw [getStorVal_afterStore, afterSload_getStor, hsup']
  set M1 := ((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 224 d.toBytes).write 192 (3 : B256).toBytes
  have hM1 : M1.size = 256 := by simp only [M1, Mem.size_write_word_at, hM]; decide
  have hwf1 : Mem.Wf M1 := ((hwf0.write _ _).write _ _)
  set M3 := M1.write 320 v.toBytes
  have hM3 : M3.size = 352 := by simp only [M3, Mem.size_write_word_at, hM1]; decide
  refine ⟨3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19, fun G hG => ?_⟩
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  have hwf3 : Mem.Wf M3 := hwf1.write _ _
  set b4 := (afterSstore sevm (afterSload sevm b2 s2) s2 (y + v)).addLog
    ⟨sevm.currentTarget, [transferTopic, 0, d], v.toBytes⟩
  set M5 := M3.write 0 (1 : B256).toBytes
  refine ⟨((St b4 [] M5 G).memRead 0 32).2.withOutput (1 : B256).toBytes, ?_, rfl, ?_⟩
  · unfold entrySt
    rw [show G + (3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19) = G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x05) (l := 0x78) (fail := t_0574_c0) hv (by simp) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x05) (l := 0x89) (fail := t_0585_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hd0]; exact hd) (by simp) ?_
    refine rx_push (w := vyMinterSlot) rfl (by simp) ?_
    refine rx_sload_sel hfork (by simp) ?_
    refine rx_caller (by simp) ?_
    refine rx_eq (v := 1) ?_ (by simp) ?_
    · have : b.getStorVal sevm.currentTarget vyMinterSlot = sevm.caller.toB256 := hmin
      simp [B256.eqCheck, this]
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    refine rx_push (w := 0) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_xor (v := d) (B256.xor_zero d) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ hnz (rx_dest ?_)
    refine rx_push (w := vySupplySlot) rfl (by simp) ?_
    refine rx_vyAddStore (p := 0x24) (h := 0x05) (l := 0xbd) (fail := t_05b9_c0) hfork hstatic
      (by rw [hv1, getStorVal_afterSload]; exact hsup) (by omega) (by simp) ?_
    rw [hv1]
    refine rx_push (w := 3) h3 (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_vyAddStore (p := 0x24) (h := 0x05) (l := 0xeb) (fail := t_05e7_c0) hfork hstatic
      (by rw [hv1]; show y.toNat + v.toNat < 2 ^ 256; rw [hy]; exact hbal) (by omega) (by simp) ?_
    rw [hv1]
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hv1]
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 12) ?_ (M' := M3) (by rw [h320]) ?_
    · rw [h320, St.extCost_eq hM1]; decide
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_push (w := 0) (by decide) (by simp) ?_
    refine rx_push (w := transferTopic) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_log3 (c := 1756) (data := v.toBytes) hstatic ?_ ?_ ?_ ?_
    · rw [h320, h32, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3])]; decide
    · rw [h320, h32]; exact Mem.read_write_word_of_wf hwf1 320 v
    · rw [h320, h32]; exact read_covered hM3 (by decide) (by decide)
    refine rx_push (w := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 3) ?_ (M' := M5) (by rw [h0]) ?_
    · rw [h0, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3]; omega)]; rfl
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_return ?_ ?_
    · have hM5 : M5.size = 352 := by simp only [M5, Mem.size_write_word_at, hM3]; decide
      rw [h0, h32, St, Devm.extCost_zero_of_le (by rw [hM5]) (by rw [hM5]; omega)]
    · rw [h0, h32]; exact Mem.read_write_word_of_wf hwf3 0 1
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore, getStor_afterStore,
        afterSload_getStor, hy, hsup']
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha,
        afterSload_getStor]
    · rw [logs_St_return, logs_addLog, logs_afterStore, logs_afterStore, afterSload_logs]
    · cases ho
      exact output_St_return _ _ _ _ _ _ _

-- SEGMENT: liveMintBurn (see `live_mint`)
theorem live_burnFrom (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawBurnFrom sevm stor₀ = some r) : BodyLive sevm b t_0644_c0 r := by
  simp only [rawBurnFrom] at hr
  split_ifs at hr with hg
  obtain ⟨hv, hd, hmin, hnz, hsup, hbal⟩ := hg
  have hr' := (Option.some.inj hr).symm
  subst hr'
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have h3 : Bytes.toB256 [0x03] = 3 := by decide
  have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  set d := Sevm.argWord sevm 0
  set v := Sevm.argWord sevm 1
  set s2 := mapSlot 3 d
  set b1 := afterSload sevm b vyMinterSlot
  set sup := b1.getStorVal sevm.currentTarget vySupplySlot
  have hsup' : sup = (stor₀).get vySupplySlot := getStorVal_afterSload
  set b2 := afterSstore sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v)
  set y := b2.getStorVal sevm.currentTarget s2
  have hy : y = (((stor₀).set vySupplySlot ((stor₀).get vySupplySlot - v)).get s2) := by
    show b2.getStorVal _ _ = _
    rw [getStorVal_afterStore, afterSload_getStor, hsup']
  set M1 := ((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 224 d.toBytes).write 192 (3 : B256).toBytes
  have hM1 : M1.size = 256 := by simp only [M1, Mem.size_write_word_at, hM]; decide
  have hwf1 : Mem.Wf M1 := ((hwf0.write _ _).write _ _)
  set M3 := M1.write 320 v.toBytes
  have hM3 : M3.size = 352 := by simp only [M3, Mem.size_write_word_at, hM1]; decide
  refine ⟨3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19, fun G hG => ?_⟩
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  have hwf3 : Mem.Wf M3 := hwf1.write _ _
  set b4 := (afterSstore sevm (afterSload sevm b2 s2) s2 (y - v)).addLog
    ⟨sevm.currentTarget, [transferTopic, d, 0], v.toBytes⟩
  set M5 := M3.write 0 (1 : B256).toBytes
  refine ⟨((St b4 [] M5 G).memRead 0 32).2.withOutput (1 : B256).toBytes, ?_, rfl, ?_⟩
  · unfold entrySt
    rw [show G + (3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19) = G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x06) (l := 0x4e) (fail := t_064a_c0) hv (by simp) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x06) (l := 0x5f) (fail := t_065b_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hd0]; exact hd) (by simp) ?_
    refine rx_push (w := vyMinterSlot) rfl (by simp) ?_
    refine rx_sload_sel hfork (by simp) ?_
    refine rx_caller (by simp) ?_
    refine rx_eq (v := 1) ?_ (by simp) ?_
    · have : b.getStorVal sevm.currentTarget vyMinterSlot = sevm.caller.toB256 := hmin
      simp [B256.eqCheck, this]
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    refine rx_push (w := 0) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_xor (v := d) (B256.xor_zero d) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ hnz (rx_dest ?_)
    refine rx_push (w := vySupplySlot) rfl (by simp) ?_
    refine rx_vySubStore (p := 0x24) (h := 0x06) (l := 0x91) (fail := t_068d_c0) hfork hstatic
      (by rw [hv1, getStorVal_afterSload]; exact hsup) (by omega) (by simp) ?_
    rw [hv1]
    refine rx_push (w := 3) h3 (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_vySubStore (p := 0x24) (h := 0x06) (l := 0xbd) (fail := t_06b9_c0) hfork hstatic
      (by rw [hv1]; show v ≤ y; rw [hy]; exact hbal) (by omega) (by simp) ?_
    rw [hv1]
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hv1]
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 12) ?_ (M' := M3) (by rw [h320]) ?_
    · rw [h320, St.extCost_eq hM1]; decide
    refine rx_push (w := 0) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_push (w := transferTopic) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_log3 (c := 1756) (data := v.toBytes) hstatic ?_ ?_ ?_ ?_
    · rw [h320, h32, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3])]; decide
    · rw [h320, h32]; exact Mem.read_write_word_of_wf hwf1 320 v
    · rw [h320, h32]; exact read_covered hM3 (by decide) (by decide)
    refine rx_push (w := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 3) ?_ (M' := M5) (by rw [h0]) ?_
    · rw [h0, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3]; omega)]; rfl
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_return ?_ ?_
    · have hM5 : M5.size = 352 := by simp only [M5, Mem.size_write_word_at, hM3]; decide
      rw [h0, h32, St, Devm.extCost_zero_of_le (by rw [hM5]) (by rw [hM5]; omega)]
    · rw [h0, h32]; exact Mem.read_write_word_of_wf hwf3 0 1
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore, getStor_afterStore,
        afterSload_getStor, hy, hsup']
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha,
        afterSload_getStor]
    · rw [logs_St_return, logs_addLog, logs_afterStore, logs_afterStore, afterSload_logs]
    · cases ho
      exact output_St_return _ _ _ _ _ _ _

-- SEGMENT: liveStringViews (116 + 116 nodes; `name` and `symbol`, one shape)
/-- `name()` and `symbol()`.  Proof sketch: guard; `mstore(0xc0, slot); keccak(0xc0, 0x20)` is
the base; the loop (first iteration inlined, then entry 9 / 10 with join 5 / 6) copies storage
words `base + i` to memory `0x180 + 32 i` while `32 i ≤ L + 32` and `i < 3` (`2` for `symbol`),
counter at `0x120`: `SFunc.RunExactCut.iterate` with the invariant "memory reads the first `i`
words"; then the join: `CALLDATACOPY` from `CALLDATASIZE` zero-fills `ceil32 L - L` bytes after the
string (the `(L - 1) mod 32` arithmetic is `ceil32`, including `L = 0` by wrapping), `mstore(0x160,
0x20)`, `return(0x160, ceil32 (0x40 + L))`, which reads `abiString (vyStrOf stor base n)`.
The same loop shape as `set_name`'s, reversed (storage to memory): one generic lemma serves both
views. -/
theorem live_name (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawName sevm stor₀ = some r) : BodyLive sevm b t_0716_c0 r := by
  sorry

-- SEGMENT: liveStringViews (see `live_name`)
theorem live_symbol (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawSymbol sevm stor₀ = some r) : BodyLive sevm b t_07ca_c0 r := by
  sorry

end

/-- The raw effect of body `k` succeeds with `r` and body `k` runs to it (all bodies but
`set_name`). -/
theorem live_at {sevm : Sevm} {b : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {k : Nat} {f : SFunc} {ow : Option B256} {r : Raw}
    (hk1 : k ≠ 1) (hf : bodies[k]? = some f)
    (hr : rawOf k sevm ow (Devm.getStor b sevm.currentTarget) = some r) : BodyLive sevm b f r := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [bodies, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hf
  all_goals try subst hf
  · exact live_setMinter hfork hstatic hr
  · exact absurd rfl hk1
  · exact live_totalSupply hfork hr
  · exact live_allowance hfork hr
  · exact live_transfer hfork hstatic hr
  · exact live_transferFrom hfork hstatic hr
  · exact live_approve hfork hstatic hr
  · exact live_mint hfork hstatic hr
  · exact live_burnFrom hfork hstatic hr
  · exact live_name hfork hr
  · exact live_symbol hfork hr
  · exact live_decimals hfork hr
  · exact live_balanceOf hfork hr

/-! ## `set_name`: live when the owner answers -/

/-- The static call `set_name` makes answers `w` whenever it is made with at least `Gc` gas and
the owner calldata in its input window, and leaves at least `R` gas: a premise about the
contract at the stored minter, over any call-site memory and stack below. -/
def OwnerCallOk (sevm : Sevm) (b : Devm) (w : B256) (R Gc : Nat) : Prop :=
  ∀ (S : List B256) (M : Mem) (G : Nat), Gc ≤ G → G < 2 ^ 256 →
    (M.read 0x23c 4).1 = ownerCalldata →
    ∃ d out, Ninst.RunCompiled sevm
        (St (afterSload sevm b vyMinterSlot) (Nat.toB256 G ::
          b.getStorVal sevm.currentTarget vyMinterSlot :: 0x23c :: 4 :: 0x280 :: 0x20 :: S) M G)
        (.exec .staticcall) d ∧
      StaticCallPost (afterSload sevm b vyMinterSlot) d S M 0x23c 4 0x280 0x20 1 out ∧
      32 ≤ out.length ∧ Bytes.toB256 (out.take 32) = w ∧ R ≤ d.gasLeft

-- SEGMENT: liveSetName (217 nodes; after `safeSetName`, whose loop lemma it mirrors)
/-- **`set_name`, forward**, given the owner's answer.  There are a gas amount `R` the rest of
the body needs after the call and a prefix cost `P` (both fixed by `b`) such that, if the owner
call answers the caller leaving at least `R` gas whenever made with at least `Gc`, every frame
gas `G ≥ Gc + P` runs the body to the raw effect.  Gas after the call is the callee's business,
so the final gas is not stated.

Proof sketch: the forward walk of `safeSetName`'s prefix (`rx_calldatacopy`s with their
expansion to `0x200`, length guards from `rawSetName`), `mstore(0x220, sel)` (expansion to
`0x240`), `rx_sload_sel`, `rx_gas` (pushes the gas left, `G - P + …`, below `2^256`), then the
call step from `OwnerCallOk` (`rx_staticcall`'s continuation form, flag `1`), the three checks,
and the two copy loops by `SFunc.RunExactCut.iterate` at the `sstoreCost`s of the string
slots, all within `R`. -/
theorem live_setName {sevm : Sevm} {b : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw}
    (hr : rawSetName sevm (Devm.getStor b sevm.currentTarget) (some sevm.caller.toB256) =
      some r) :
    ∃ R P, ∀ Gc, OwnerCallOk sevm b sevm.caller.toB256 R Gc → ∀ G, Gc + P ≤ G → G < 2 ^ 256 →
      ∃ post, SFunc.RunExact prog sevm (entrySt sevm b G) t_00f1_c0 (.halted post) ∧
        Lands sevm b post r := by
  sorry

end Blanc.Lift.Curve3Crv
