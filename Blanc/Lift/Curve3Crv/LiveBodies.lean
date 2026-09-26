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
  simp only [rawApprove] at hr
  split_ifs at hr with hg
  obtain ⟨hv, hp, hz⟩ := hg
  have hr' := (Option.some.inj hr).symm
  subst hr'
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have h4 : Bytes.toB256 [0x04] = 4 := by decide
  have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  set p := Sevm.argWord sevm 0
  set v := Sevm.argWord sevm 1
  set slot := mapSlot (mapSlot 4 sevm.caller.toB256) p
  -- the join (entry 4) and the write, forward, from a base with `b`'s storage and logs
  have tail : ∀ (b' : Devm) (M' : Mem) (n c1 : Nat) (flag : B256), Mem.Wf M' → M'.size = n →
      n ≤ 256 → n % 32 = 0 →
      gVerylow + (calculateMemoryGasCost (memExtSize n 224 32) - calculateMemoryGasCost n) = c1 →
      (∀ a, Devm.getStor b' a = Devm.getStor b a) → b'.logs = b.logs → flag ≠ 0 →
      ∀ G, gCallStipend < G → ∃ post,
        SFunc.RunExact prog sevm (St b' [flag] M' (G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + sstoreCost sevm b' slot v + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + c1 + 3 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 1 + 1)) t_04f6_c4 (.halted post) ∧
          post.gasLeft = G ∧ Lands sevm b post ((stor₀).set slot v,
            [⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, p], v.toBytes⟩],
            some (1 : B256).toBytes) := by
    intro b' M' n c1 flag hwf hMn hn hn32 hc1 hst hlg hflag G hG
    set M1 := (M'.write 224 sevm.caller.toB256.toBytes).write 192 (4 : B256).toBytes
    have hs1 : (M'.write 224 sevm.caller.toB256.toBytes).size = 256 := by
      rw [Mem.size_write_word_at, hMn]
      split_ifs with h
      · omega
      · rfl
    have hM1 : M1.size = 256 := by
      simp only [M1]; rw [Mem.size_write_word_at, hs1]; rfl
    set M2 := (M1.write 224 p.toBytes).write 192 (mapSlot 4 sevm.caller.toB256).toBytes
    have hM2 : M2.size = 256 := by simp only [M2, Mem.size_write_word_at, hM1]; decide
    have hwf2 : Mem.Wf M2 := ((((hwf.write _ _).write _ _).write _ _).write _ _)
    set M3 := M2.write 320 v.toBytes
    have hM3 : M3.size = 352 := by simp only [M3, Mem.size_write_word_at, hM2]; decide
    have hwf3 : Mem.Wf M3 := hwf2.write _ _
    set b4 := (afterSstore sevm b' slot v).addLog
      ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, p], v.toBytes⟩
    set M5 := M3.write 0 (1 : B256).toBytes
    refine ⟨((St b4 [] M5 G).memRead 0 32).2.withOutput (1 : B256).toBytes, ?_, rfl, ?_⟩
    · unfold t_04f6_c4 t_04f7_c4
      refine rx_dest (rx_dest ?_)
      refine rx_push rfl (by simp) ?_
      refine rx_branch_succ hflag (rx_dest ?_)
      refine rx_push rfl (by simp) ?_
      refine rx_calldataload (by simp) ?_
      rw [hv1]
      refine rx_push (w := 4) h4 (by simp) ?_
      refine rx_caller (by simp) ?_
      refine rx_vySlot hMn hn hn32 hc1 (by simp) ?_
      refine rx_push rfl (by simp) ?_
      refine rx_calldataload (by simp) ?_
      rw [hd0]
      refine rx_vySlot (c1 := 3) hM1 (by omega) (by decide) (by decide) (by simp) ?_
      refine rx_sstore hfork (by omega) hstatic ?_
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
      refine rx_push (w := approvalTopic) (by decide) (by simp) ?_
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
      · rw [getStor_St_return, getStor_addLog, afterSstore_getStor_self, hst]
      · rw [getStor_St_return, getStor_addLog, afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), hst]
      · rw [logs_St_return, logs_addLog, afterSstore_logs, hlg]
      · cases ho
        exact output_St_return _ _ _ _ _ _ _
  by_cases hv0 : v = 0
  · refine ⟨3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + sstoreCost sevm b slot v + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 1 + 1 + 8 + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 34 + 19, fun G hG => ?_⟩
    obtain ⟨post, hrun, hg, hl⟩ := tail b _ 192 9 1 hwf0 hM (by omega) (by decide) (by decide)
      (fun _ => rfl) rfl (by decide) G hG
    refine ⟨post, ?_, hg, hl⟩
    unfold entrySt
    rw [show G + (3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + sstoreCost sevm b slot v + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 1 + 1 + 8 + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 34 + 19) = G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + sstoreCost sevm b slot v + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 1 + 1 + 8 + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x04) (l := 0xb5) (fail := t_04b1_c0) hv (by simp) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x04) (l := 0xc6) (fail := t_04c2_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hd0]; exact hp) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hv1]
    refine rx_iszero (v := 1) (by simp [B256.eqCheck, hv0]) (by simp) ?_
    refine rx_iszero (v := 0) (by simp [B256.eqCheck]) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branch_zero ?_
    unfold t_04d1_c0
    refine rx_push (w := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_jump (g := t_04f6_c4) rfl ?_
    convert hrun using 2
  · have hcur : (stor₀).get slot = 0 := hz.resolve_left hv0
    set MB := ((((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 224 sevm.caller.toB256.toBytes).write
      192 (4 : B256).toBytes).write 224 p.toBytes).write 192 (mapSlot 4 sevm.caller.toB256).toBytes
    have hMA : (((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 224
        sevm.caller.toB256.toBytes).write 192 (4 : B256).toBytes).size = 256 := by
      rw [Mem.size_write_word_at, Mem.size_write_word_at, hM]; decide
    have hMB : MB.size = 256 := by
      simp only [MB]; rw [Mem.size_write_word_at, Mem.size_write_word_at, hMA]; decide
    have hwfB : Mem.Wf MB := ((((hwf0.write _ _).write _ _).write _ _).write _ _)
    refine ⟨3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + sstoreCost sevm (afterSload sevm b slot) slot v + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 1 + 1 + 3 + sloadCost sevm b slot + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 34 + 19, fun G hG => ?_⟩
    obtain ⟨post, hrun, hg, hl⟩ := tail (afterSload sevm b slot) MB 256 3 1 hwfB hMB (by omega)
      (by decide) (by decide) (fun a => afterSload_getStor _ _ _ _) (afterSload_logs _ _ _)
      (by decide) G hG
    refine ⟨post, ?_, hg, hl⟩
    unfold entrySt
    rw [show G + (3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + sstoreCost sevm (afterSload sevm b slot) slot v + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 1 + 1 + 3 + sloadCost sevm b slot + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 34 + 19) = G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 2 + 3 + 3 + 12 + 3 + 3 + 3 + sstoreCost sevm (afterSload sevm b slot) slot v + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 1 + 10 + 3 + 1 + 1 + 3 + sloadCost sevm b slot + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 2 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x04) (l := 0xb5) (fail := t_04b1_c0) hv (by simp) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x04) (l := 0xc6) (fail := t_04c2_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hd0]; exact hp) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hv1]
    refine rx_iszero (v := 0) (by simp [B256.eqCheck, hv0]) (by simp) ?_
    refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    refine rx_push (w := 4) h4 (by simp) ?_
    refine rx_caller (by simp) ?_
    refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd0]
    refine rx_vySlot (S := []) (c1 := 3) hMA (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_sload_sel hfork (by simp) ?_
    refine rx_iszero (v := 1) ?_ (by simp) hrun
    have : b.getStorVal sevm.currentTarget slot = 0 := hcur
    simp only [B256.eqCheck]
    rw [ite_eq_left this]

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

/-! ### The string views' shared pieces -/

theorem ceil32_eq (L : Nat) : ceil32 L = L + 31 - (L + 31) % 32 := by
  unfold ceil32
  rcases h : L % 32 with _ | m
  · simp only; omega
  · simp only; omega

/-- Reading calldata from its own size reads zeros. -/
theorem sliceD_data_end (bs : Bytes) (z : Nat) : bs.sliceD bs.length z 0 = List.replicate z 0 := by
  unfold List.sliceD
  rw [List.drop_length]
  induction z with
  | zero => rfl
  | succ z ih => simp [List.takeD, ih, List.replicate_succ]

/-- The string views' join: zero-pad the string, `mstore(0x160, 0x20)`, and return the ABI
string from `0x160`, over a memory whose word at `0x180` is the length and whose bytes at
`0x1a0` are the string. -/
theorem live_strJoin (hcd : sevm.data.length < 2 ^ 256) {M : Mem} {sz : Nat} {Lw : B256}
    {str : Bytes} {a1 a2 a3 a4 a5 a6 : B256} (hwf : Mem.Wf M) (hs : M.size = sz)
    (hsz32 : sz % 32 = 0) (hsz : 0x1a0 + ceil32 Lw.toNat ≤ sz) (hL : Lw.toNat ≤ 64)
    (hLw : (M.read 0x180 32).1 = Lw.toBytes) (hstr : (M.read 0x1a0 Lw.toNat).1 = str)
    (hlen : str.length = Lw.toNat) (bb : Devm) (G : Nat) :
    ∃ post, SFunc.RunExact prog sevm
        (St bb [a1, a2, a3, a4, a5, a6] M (G + 141 + 3 * ceilDiv (ceil32 Lw.toNat - Lw.toNat) 32)) t_0774_c5
        (.halted post) ∧
      post.gasLeft = G ∧ (∀ a, Devm.getStor post a = Devm.getStor bb a) ∧
      post.logs = bb.logs ∧ post.output = abiString str := by
  set L := Lw.toNat with hLdef
  have hc := ceil32_eq L
  set z := ceil32 L - L with hzdef
  have hz : z = 31 - (L + 31) % 32 := by omega
  have hLt : L < 2 ^ 256 := by omega
  -- the word arithmetic
  have h1a0 : (Bytes.toB256 [0x01, 0xa0]).toNat = 416 := by decide
  have hX : (Bytes.toB256 [0x01, 0xa0] + Lw).toNat = 416 + L := by
    rw [B256.toNat_add, h1a0, Nat.lo_eq_of_lt (by omega)]
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h1f : (Bytes.toB256 [0x1f]).toNat = 31 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hmod : ∀ x : B256, x.toNat < 2 ^ 256 → ((x - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat
      = (x.toNat + 31) % 32 := by
    intro x _
    rw [B256.toNat_mod (by decide), B256.toNat_sub, h1, h20, Nat.lo]
    omega
  set m := (Lw - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]
  have hm : m.toNat = (L + 31) % 32 := hmod Lw (B256.toNat_lt Lw)
  have hL31 : (Lw + Bytes.toB256 [0x1f]).toNat = L + 31 := by
    rw [B256.toNat_add, h1f, Nat.lo_eq_of_lt (by omega)]
  have hsub1 : (Lw + Bytes.toB256 [0x1f] - m).toNat = L + 31 - (L + 31) % 32 := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hm, hL31]; omega), hm, hL31]
  have hzB : (Lw + Bytes.toB256 [0x1f] - m - Lw).toNat = z := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hsub1]; omega), hsub1]
    omega
  set A := Lw + Bytes.toB256 [0x40]
  have hA : A.toNat = L + 64 := by
    rw [B256.toNat_add, h40, Nat.lo_eq_of_lt (by omega)]
  set m' := (A - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]
  have hm' : m'.toNat = (L + 63) % 32 := by rw [hmod A (B256.toNat_lt A), hA]; omega
  have hA31 : (A + Bytes.toB256 [0x1f]).toNat = L + 95 := by
    rw [B256.toNat_add, h1f, hA, Nat.lo_eq_of_lt (by omega)]
  have hret : (A + Bytes.toB256 [0x1f] - m').toNat = 64 + ceil32 L := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hm', hA31]; omega), hm', hA31]
    omega
  -- the memory
  have hrd : ∀ i n, (M.read i n).1 = M.data.toList.sliceD i n 0 := (Mem.reads_data M).read
  set M1 := M.write (416 + L) (List.replicate z 0)
  have hM1s : M1.size = sz := by
    rw [Mem.size_write_of_le (by rw [List.length_replicate, hs]; omega), hs]
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hr1 : Mem.Reads M1 (Bytes.writeAt M.data.toList (416 + L) (List.replicate z 0)) :=
    (Mem.reads_data M).write hwf _ _
  set M2 := M1.write 0x160 (Bytes.toB256 [0x20]).toBytes
  have hM2s : M2.size = sz := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hM1s]; omega), hM1s]
  have hr2 := hr1.write hwf1 0x160 (Bytes.toB256 [0x20]).toBytes
  have hread180 : Bytes.toB256 (M2.read 0x180 32).1 = Lw := by
    rw [hr2.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hLw, B256.toB256_toBytes]
  have h180 : (Bytes.toB256 [0x01, 0x80]).toNat = 384 := by decide
  have h160 : (Bytes.toB256 [0x01, 0x60]).toNat = 352 := by decide
  have hout : (M2.read 352 (64 + ceil32 L)).1 = abiString str := by
    rw [hr2.read, show 64 + ceil32 L = 32 + (32 + (L + z)) by omega, List.sliceD_split,
      List.sliceD_split, List.sliceD_split, sliceD_word_same,
      show (352 : Nat) + 32 = 384 from rfl, show (384 : Nat) + 32 = 416 from rfl,
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hLw,
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hstr,
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]),
      Nat.sub_self, Bytes.sliceD_zero_length (List.length_replicate ..)]
    unfold abiString
    rw [hlen, hLdef, toB256_toNat, show Bytes.toB256 [0x20] = (32 : B256) by decide]
    simp only [List.append_assoc]
    rfl
  refine ⟨((St bb [] M2 G).memRead (Bytes.toB256 [0x01, 0x60]).toNat
    (A + Bytes.toB256 [0x1f] - m').toNat).2.withOutput (abiString str), ?_, rfl,
    fun a => rfl, rfl, rfl⟩
  rw [show G + 141 + 3 * ceilDiv z 32 = G + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 +
    3 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + (3 + 3 * ceilDiv z 32) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 3 +
    5 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 2 + 2 + 2 + 2 + 1 by omega]
  unfold t_0774_c5
  refine rx_dest ?_
  refine rx_pop (rx_pop (rx_pop (rx_pop (rx_pop (rx_pop ?_)))))
  refine rx_push rfl (by simp) ?_
  refine rx_mload (c := 3) (v := Lw) ?_ (by rw [h180, hLw, B256.toB256_toBytes])
    (by rw [h180]; exact read_covered hs hsz32 (by omega)) (by simp) ?_
  · rw [h180, St, Devm.extCost_zero_of_le (by rw [hs]; exact hsz32) (by rw [hs]; omega)]; rfl
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_add (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_sub (by simp) ?_
  refine rx_mod (v := m) rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_add (by simp) ?_
  refine rx_sub (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_sub (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_calldatacopy (c := 3 + 3 * ceilDiv z 32) (M' := M1) ?_ ?_ ?_
  · rw [hzB, hX, St, Devm.extCost_zero_of_le (by rw [hs]; exact hsz32) (by rw [hs]; omega)]; rfl
  · rw [hX, hzB, B256.toNat_toB256_of_lt hcd, sliceD_data_end]
  refine rx_pop (rx_pop ?_)
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_mstore (c := 3) ?_ (M' := M2) (by rw [h160]) ?_
  · rw [h160, St, Devm.extCost_zero_of_le (by rw [hM1s]; exact hsz32) (by rw [hM1s]; omega)]; rfl
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_mload (c := 3) (v := Lw) ?_ (by rw [h180]; exact hread180)
    (by rw [h180]; exact read_covered hM2s hsz32 (by omega)) (by simp) ?_
  · rw [h180, St, Devm.extCost_zero_of_le (by rw [hM2s]; exact hsz32) (by rw [hM2s]; omega)]; rfl
  refine rx_add (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_sub (by simp) ?_
  refine rx_mod (v := m') rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_add (by simp) ?_
  refine rx_sub (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp) ?_
  refine rx_return ?_ (by rw [h160, hret]; exact hout)
  rw [h160, hret, St, Devm.extCost_zero_of_le (by rw [hM2s]; exact hsz32) (by rw [hM2s]; omega)]

/-- The string views' body: the `CALLVALUE` guard, `mstore(0xc0, sl); keccak(0xc0, 0x20)` for
the base, the length word, the counter at `0x120`, then the load loop `loopT`. -/
def strBody (h0 h1 sl cp : UInt8) (fail loopT : SFunc) : SFunc :=
  .next (.reg .callvalue) (.next (.reg .iszero) (.next (.push [h0, h1] (by simp))
  (.branch fail (.dest (.next (.push [sl] (by simp)) (.next (.reg (.dup 0))
  (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide))
  (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.push [0x01, 0x80] (by decide))
  (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .sload) (.next (.reg .add)
  (.next (.push [0x01, 0x20] (by decide)) (.next (.push [0x00] (by decide))
  (.next (.push [cp] (by simp)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3))
  (.next (.reg .mstore) (.next (.reg .add) loopT)))))))))))))))))))))))

/-- The string views' prefix, forward, to the load loop's head. -/
theorem rx_strPrefix (hfork : CoveredFork sevm.benvStat.fork) (hv : sevm.value = 0)
    {h0 h1 sl cp : UInt8} {fail loopT : SFunc} {G : Nat} {o : Outcome}
    (kk : SFunc.RunExact prog sevm
      (St (afterSload sevm b (Bytes.toB256 [sl]).toBytes.keccak)
        (vyLoadStack (Bytes.toB256 [cp] + Nat.toB256 0)
          (b.getStorVal sevm.currentTarget (Bytes.toB256 [sl]).toBytes.keccak + Bytes.toB256 [0x20])
          0x180 (Bytes.toB256 [sl]).toBytes.keccak [Bytes.toB256 [sl]])
        (((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 192 (Bytes.toB256 [sl]).toBytes).write
          288 (Nat.toB256 0).toBytes) G) loopT o) :
    SFunc.RunExact prog sevm
      (entrySt sevm b (G + 118 + sloadCost sevm b (Bytes.toB256 [sl]).toBytes.keccak))
      (strBody h0 h1 sl cp fail loopT) o := by
  have hM0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  set M1 := (vyMem Mem.empty (Sevm.dataWord sevm 0)).write 192 (Bytes.toB256 [sl]).toBytes
  have hM1 : M1.size = 224 := by simp only [M1, Mem.size_write_word_at, hM0]; decide
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 192 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h120 : (Bytes.toB256 [0x01, 0x20]).toNat = 288 := by decide
  unfold entrySt strBody
  rw [show G + 118 + sloadCost sevm b (Bytes.toB256 [sl]).toBytes.keccak =
    G + 3 + 12 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b (Bytes.toB256 [sl]).toBytes.keccak +
      3 + 3 + 3 + 36 + 3 + 3 + 6 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 by omega]
  refine rx_callvalue (by simp) ?_
  refine rx_iszero (v := 1) (by simp [hv, B256.eqCheck]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) (rx_dest ?_)
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_mstore (c := 6) ?_ (M' := M1) (by rw [hc0]) ?_
  · rw [hc0, St.extCost_eq hM0]; decide
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_keccak (c := 36) ?_ (by rw [hc0, h20, Mem.read_write_word_of_wf hwf0])
    (by rw [hc0, h20]; exact read_covered hM1 (by decide) (by decide)) (by simp) ?_
  · rw [hc0, h20, St, Devm.extCost_zero_of_le (by rw [hM1]) (by rw [hM1])]; decide
  refine rx_push (w := 0x180) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_sload_sel hfork (by simp) ?_
  refine rx_add (by simp) ?_
  refine rx_push (w := 0x120) (by decide) (by simp) ?_
  refine rx_push (w := Nat.toB256 0) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 3) rfl (by simp) ?_
  refine rx_mstore (c := 12) ?_ (by rfl) ?_
  · show gVerylow + (St _ _ M1 _).extCost [⟨(0x120 : B256).toNat, 32⟩] = 12
    rw [St.extCost_eq hM1]; decide
  exact rx_add (by simp) kk

/-- **The string views, forward**, for either view: `sl` the variable's slot (its base is
`keccak(sl)`), `cp` the loop's cap (`n + 1` words: the length and `n` data words). -/
theorem live_strView (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    (hv : sevm.value = 0) {h0 h1 sl cp : UInt8} {fail : SFunc} {e0 e1 x0 x1 r0 r1 : UInt8}
    {j k n : Nat} {joinT : SFunc} (hjT : joinT = t_0774_c5)
    (hk : prog[k]? = some (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k joinT))
    (hj : prog[j]? = some joinT)
    (hcase : (cp = 3 ∧ n = 2 ∧ ((stor₀).get (Bytes.toB256 [sl]).toBytes.keccak).toNat ≤ 64) ∨
      (cp = 2 ∧ n = 1 ∧ ((stor₀).get (Bytes.toB256 [sl]).toBytes.keccak).toNat ≤ 32)) :
    BodyLive sevm b (strBody h0 h1 sl cp fail (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k joinT))
      (stor₀, [], some (abiString (vyStrOf stor₀ (Bytes.toB256 [sl]).toBytes.keccak n))) := by
  subst hjT
  set base := (Bytes.toB256 [sl]).toBytes.keccak with hbase
  set Lw := b.getStorVal sevm.currentTarget base with hLwdef
  have hLst : (stor₀).get base = Lw := rfl
  rw [hLst] at hcase
  set L := Lw.toNat with hLdef
  set capB := Bytes.toB256 [cp] + Nat.toB256 0
  set lp := Lw + Bytes.toB256 [0x20]
  have hlp : lp.toNat = L + 32 := by
    rw [B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by have := hcase; omega)]
  set S0 := vyLoadStack capB lp 0x180 base [Bytes.toB256 [sl]]
  set b1 := afterSload sevm b base
  set b2 := afterSload sevm b1 (base + Nat.toB256 0)
  set b3 := afterSload sevm b2 (base + Nat.toB256 1)
  set u0 := b1.getStorVal sevm.currentTarget (base + Nat.toB256 0)
  set u1 := b2.getStorVal sevm.currentTarget (base + Nat.toB256 1)
  have hu0 : u0 = Lw := by
    show (afterSload sevm b base).getStorVal _ _ = _
    rw [getStorVal_afterSload, show base + Nat.toB256 0 = base by
      apply B256.toNat_inj
      rw [B256.toNat_add, B256.toNat_toB256_of_lt (by decide), Nat.add_zero,
        Nat.lo_eq_of_lt (B256.toNat_lt _)]]
  have hu1 : u1 = (stor₀).get (base + Nat.toB256 (0 + 1)) := by
    show (afterSload sevm (afterSload sevm b base) _).getStorVal _ _ = _
    rw [getStorVal_afterSload, getStorVal_afterSload]; rfl
  have hM0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  set M1 := (vyMem Mem.empty (Sevm.dataWord sevm 0)).write 192 (Bytes.toB256 [sl]).toBytes
  have hM1 : M1.size = 224 := by simp only [M1, Mem.size_write_word_at, hM0]; decide
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  set M2 := M1.write 288 (Nat.toB256 0).toBytes
  have hM2 : M2.size = 320 := by simp only [M2, Mem.size_write_word_at, hM1]; decide
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hc2 : (M2.read 0x120 32).1 = (Nat.toB256 0).toBytes := Mem.read_write_word_of_wf hwf1 _ _
  set M3 := (M2.write (384 + 32 * 0) u0.toBytes).write 0x120 (Nat.toB256 (0 + 1)).toBytes
  have hM3 : M3.size = 416 := by
    simp only [M3, Mem.size_write_word_at, hM2]; decide
  have hwf3 : Mem.Wf M3 := (hwf2.write _ _).write _ _
  have hc3 : (M3.read 0x120 32).1 = (Nat.toB256 1).toBytes :=
    Mem.read_write_word_of_wf (hwf2.write _ _) _ _
  set M4 := (M3.write (384 + 32 * 1) u1.toBytes).write 0x120 (Nat.toB256 (1 + 1)).toBytes
  have hM4 : M4.size = 448 := by
    simp only [M4, Mem.size_write_word_at, hM3]; decide
  have hwf4 : Mem.Wf M4 := (hwf3.write _ _).write _ _
  have hc4 : (M4.read 0x120 32).1 = (Nat.toB256 2).toBytes :=
    Mem.read_write_word_of_wf (hwf3.write _ _) _ _
  -- images
  have hr2 := Mem.reads_data M2
  have hr4 := ((((hr2.write hwf2 (384 + 32 * 0) u0.toBytes).write (hwf2.write _ _) 0x120
    (Nat.toB256 (0 + 1)).toBytes).write hwf3 (384 + 32 * 1) u1.toBytes).write
    (hwf3.write _ _) 0x120 (Nat.toB256 (1 + 1)).toBytes)
  have hLw4 : (M4.read 384 32).1 = Lw.toBytes := by
    rw [hr4.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]),
      show 384 - (384 + 32 * 0) = 0 from rfl, Bytes.sliceD_zero_length (B256.length_toBytes _), hu0]
  have hread4 : (M4.read 416 L).1 = u1.toBytes.take L ∨ 32 < L := by
    by_cases hL32 : L ≤ 32
    · left
      rw [hr4.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
        Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega),
        show 416 - (384 + 32 * 1) = 0 from rfl,
        sliceD_zero_take _ (by rw [B256.length_toBytes]; exact hL32)]
    · right; omega
  have hlen4 : ((M4.read 416 L).1).length = L := by rw [hr4.read, List.length_sliceD]
  have hscB := sloadCost sevm b base
  have hce0 : calculateMemoryGasCost (384 + 32 * 0 + 32) - calculateMemoryGasCost 320 = 9 := by decide
  have hce1 : calculateMemoryGasCost (384 + 32 * 1 + 32) - calculateMemoryGasCost 416 = 3 := by decide
  have h384 : (0x180 : B256).toNat = 384 := by decide
  have hlands : ∀ post : Devm, ∀ bb : Devm, (∀ a, Devm.getStor bb a = Devm.getStor b a) →
      bb.logs = b.logs → (∀ a, Devm.getStor post a = Devm.getStor bb a) → post.logs = bb.logs →
      post.output = abiString (vyStrOf stor₀ base n) →
      Lands sevm b post (stor₀, [], some (abiString (vyStrOf stor₀ base n))) := by
    intro post bb h1 h2 h3 h4 h5
    refine ⟨by rw [h3, h1], fun a _ => by rw [h3, h1], by rw [h4, h2, List.append_nil],
      fun o ho => ?_⟩
    cases ho; exact h5
  rcases hcase with ⟨rfl, rfl, hL⟩ | ⟨rfl, rfl, hL⟩
  · -- `name`: three words
    set u2 := b3.getStorVal sevm.currentTarget (base + Nat.toB256 2)
    have hu2 : u2 = (stor₀).get (base + Nat.toB256 (1 + 1)) := by
      show (afterSload sevm (afterSload sevm (afterSload sevm b base) _) _).getStorVal _ _ = _
      rw [getStorVal_afterSload, getStorVal_afterSload, getStorVal_afterSload]; rfl
    have hW : vyStrWords stor₀ base 2 = u1.toBytes ++ u2.toBytes := by
      rw [hu1, hu2]; rfl
    have hc := ceil32_eq L
    by_cases hL32 : L < 32
    · -- the test fails at the third word
      have hstr : (M4.read 416 L).1 = vyStrOf stor₀ base 2 := by
        rcases hread4 with h | h
        · rw [h, vyStrOf, hLst, hW, List.take_append_of_le_length (by rw [B256.length_toBytes]; omega)]
        · omega
      refine ⟨141 + 3 * ceilDiv (ceil32 L - L) 32 + 48 + 117 +
        sloadCost sevm b2 (base + Nat.toB256 1) + 3 + 117 + sloadCost sevm b1 (base + Nat.toB256 0) +
        9 + 118 + sloadCost sevm b base, fun G _ => ?_⟩
      obtain ⟨post, hrun, hg, hst, hlg, hout⟩ := live_strJoin hcd hwf4 hM4 (by decide)
        (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw4 hstr (by rw [← hstr, hlen4]) b3 G
      refine ⟨post, ?_, hg, hlands post b3 (fun a => by simp only [b3, b2, b1, afterSload_getStor])
        (by simp only [b3, b2, b1, afterSload_logs]) hst hlg hout⟩
      rw [show G + (141 + 3 * ceilDiv (ceil32 L - L) 32 + 48 + 117 +
        sloadCost sevm b2 (base + Nat.toB256 1) + 3 + 117 + sloadCost sevm b1 (base + Nat.toB256 0) +
        9 + 118 + sloadCost sevm b base) = G + 141 + 3 * ceilDiv (ceil32 L - L) 32 + 48 + 117 +
        sloadCost sevm b2 (base + Nat.toB256 1) + 3 + 117 + sloadCost sevm b1 (base + Nat.toB256 0) +
        9 + 118 + sloadCost sevm b base by omega]
      refine rx_strPrefix hfork hv ?_
      refine rx_vyLoadStep hfork (by simp) (i := 0) (by omega) (by decide) hwf2 hM2 (by decide)
        (by decide) h384 (by decide) (by decide) (by decide) (by decide) hce0 hc2 hk ?_
      refine rx_vyLoadStep hfork (by simp) (i := 1) (le_of_le_of_eq (by omega) hlp.symm) (by decide)
        hwf3 hM3 (by decide) (by decide) h384 (by decide) (by decide) (by decide) (by decide) hce1
        hc3 hk ?_
      exact rx_vyLoadExit (by simp) (i := 2) (lt_of_eq_of_lt hlp (by omega)) (by decide) hM4
        (by decide) (by decide) hc4 hj hrun
    · -- the third word is copied, and the counter reaches the cap
      set b4 := afterSload sevm b3 (base + Nat.toB256 2)
      set M5 := (M4.write (384 + 32 * 2) u2.toBytes).write 0x120 (Nat.toB256 (2 + 1)).toBytes
      have hM5 : M5.size = 480 := by
        simp only [M5, Mem.size_write_word_at, hM4]; decide
      have hwf5 : Mem.Wf M5 := (hwf4.write _ _).write _ _
      have hr5 := (hr4.write hwf4 (384 + 32 * 2) u2.toBytes).write (hwf4.write _ _) 0x120
        (Nat.toB256 (2 + 1)).toBytes
      have hLw5 : (M5.read 384 32).1 = Lw.toBytes := by
        rw [hr5.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hr4.read, hLw4]
      have hstr' : (M5.read 416 (32 + (L - 32))).1 = vyStrOf stor₀ base 2 := by
        rw [hr5.read, List.sliceD_split,
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hr4.read,
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]; omega),
          show 416 + 32 - (384 + 32 * 2) = 0 from rfl,
          sliceD_zero_take _ (by rw [B256.length_toBytes]; omega), hr4.read,
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]),
          show 416 - (384 + 32 * 1) = 0 from rfl,
          Bytes.sliceD_zero_length (B256.length_toBytes _), vyStrOf, hLst, hW,
          List.take_append, B256.length_toBytes,
          List.take_of_length_le (l := u1.toBytes) (by rw [B256.length_toBytes]; omega)]
      have hstr : (M5.read 416 L).1 = vyStrOf stor₀ base 2 := by
        rwa [show 32 + (L - 32) = L by omega] at hstr'
      have hlen5 : ((M5.read 416 L).1).length = L := by rw [hr5.read, List.length_sliceD]
      have hce2 : calculateMemoryGasCost (384 + 32 * 2 + 32) - calculateMemoryGasCost 448 = 3 := by
        decide
      refine ⟨141 + 3 * ceilDiv (ceil32 L - L) 32 + 117 + sloadCost sevm b3 (base + Nat.toB256 2) + 3
        + 117 + sloadCost sevm b2 (base + Nat.toB256 1) + 3 + 117 +
        sloadCost sevm b1 (base + Nat.toB256 0) + 9 + 118 + sloadCost sevm b base, fun G _ => ?_⟩
      obtain ⟨post, hrun, hg, hst, hlg, hout⟩ := live_strJoin hcd hwf5 hM5 (by decide)
        (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw5 hstr (by rw [← hstr, hlen5]) b4 G
      refine ⟨post, ?_, hg, hlands post b4
        (fun a => by simp only [b4, b3, b2, b1, afterSload_getStor])
        (by simp only [b4, b3, b2, b1, afterSload_logs]) hst hlg hout⟩
      rw [show G + (141 + 3 * ceilDiv (ceil32 L - L) 32 + 117 + sloadCost sevm b3 (base + Nat.toB256 2)
        + 3 + 117 + sloadCost sevm b2 (base + Nat.toB256 1) + 3 + 117 +
        sloadCost sevm b1 (base + Nat.toB256 0) + 9 + 118 + sloadCost sevm b base) =
        G + 141 + 3 * ceilDiv (ceil32 L - L) 32 + 117 + sloadCost sevm b3 (base + Nat.toB256 2)
        + 3 + 117 + sloadCost sevm b2 (base + Nat.toB256 1) + 3 + 117 +
        sloadCost sevm b1 (base + Nat.toB256 0) + 9 + 118 + sloadCost sevm b base by omega]
      refine rx_strPrefix hfork hv ?_
      refine rx_vyLoadStep hfork (by simp) (i := 0) (by omega) (by decide) hwf2 hM2 (by decide)
        (by decide) h384 (by decide) (by decide) (by decide) (by decide) hce0 hc2 hk ?_
      refine rx_vyLoadStep hfork (by simp) (i := 1) (le_of_le_of_eq (by omega) hlp.symm) (by decide)
        hwf3 hM3 (by decide) (by decide) h384 (by decide) (by decide) (by decide) (by decide) hce1
        hc3 hk ?_
      exact rx_vyLoadLast hfork (by simp) (i := 2) (le_of_le_of_eq (by omega) hlp.symm) (by decide)
        hwf4 hM4 (by decide) (by decide) h384 (by decide) (by decide) (by decide) (by decide) hce2
        hc4 hrun
  · -- `symbol`: two words
    have hstr : (M4.read 416 L).1 = vyStrOf stor₀ base 1 := by
      rcases hread4 with h | h
      · rw [h, vyStrOf, hLst, hu1]; rfl
      · omega
    refine ⟨141 + 3 * ceilDiv (ceil32 L - L) 32 + 117 + sloadCost sevm b2 (base + Nat.toB256 1) + 3
      + 117 + sloadCost sevm b1 (base + Nat.toB256 0) + 9 + 118 + sloadCost sevm b base,
      fun G _ => ?_⟩
    have hc := ceil32_eq L
    obtain ⟨post, hrun, hg, hst, hlg, hout⟩ := live_strJoin hcd hwf4 hM4 (by decide)
      (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw4 hstr (by rw [← hstr, hlen4]) b3 G
    refine ⟨post, ?_, hg, hlands post b3 (fun a => by simp only [b3, b2, b1, afterSload_getStor])
      (by simp only [b3, b2, b1, afterSload_logs]) hst hlg hout⟩
    rw [show G + (141 + 3 * ceilDiv (ceil32 L - L) 32 + 117 + sloadCost sevm b2 (base + Nat.toB256 1)
      + 3 + 117 + sloadCost sevm b1 (base + Nat.toB256 0) + 9 + 118 + sloadCost sevm b base) =
      G + 141 + 3 * ceilDiv (ceil32 L - L) 32 + 117 + sloadCost sevm b2 (base + Nat.toB256 1)
      + 3 + 117 + sloadCost sevm b1 (base + Nat.toB256 0) + 9 + 118 + sloadCost sevm b base by omega]
    refine rx_strPrefix hfork hv ?_
    refine rx_vyLoadStep hfork (by simp) (i := 0) (by omega) (by decide) hwf2 hM2 (by decide)
      (by decide) h384 (by decide) (by decide) (by decide) (by decide) hce0 hc2 hk ?_
    exact rx_vyLoadLast hfork (by simp) (i := 1) (le_of_le_of_eq (by omega) hlp.symm) (by decide) hwf3 hM3 (by decide)
      (by decide) h384 (by decide) (by decide) (by decide) (by decide) hce1 hc3 hrun

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

/-- `live_name` under the calldata-size bound the frame supplies (`CALLDATASIZE` is the zero-fill
source; see the note on `live_name`). -/
theorem live_name_of_cd (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) {r : Raw}
    (hr : rawName sevm stor₀ = some r) : BodyLive sevm b t_0716_c0 r := by
  unfold rawName at hr
  split_ifs at hr with h
  cases hr
  obtain ⟨hv, hL⟩ := h
  have hb : vyNameBase = (Bytes.toB256 [0x00]).toBytes.keccak := by
    rw [show Bytes.toB256 [0x00] = 0 by decide]; rfl
  rw [hb] at hL ⊢
  exact live_strView (h0 := 0x07) (h1 := 0x20) (fail := t_071c_c0) (e0 := 0x07) (e1 := 0x52)
    (x0 := 0x07) (x1 := 0x74) (r0 := 0x07) (r1 := 0x3f) hfork hcd hv rfl rfl rfl
    (Or.inl ⟨rfl, rfl, hL⟩)

/-- `live_symbol` under the calldata-size bound. -/
theorem live_symbol_of_cd (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) {r : Raw}
    (hr : rawSymbol sevm stor₀ = some r) : BodyLive sevm b t_07ca_c0 r := by
  unfold rawSymbol at hr
  split_ifs at hr with h
  cases hr
  obtain ⟨hv, hL⟩ := h
  have hb : vySymbolBase = (Bytes.toB256 [0x01]).toBytes.keccak := by
    rw [show Bytes.toB256 [0x01] = 1 by decide]; rfl
  rw [hb] at hL ⊢
  exact live_strView (h0 := 0x07) (h1 := 0xd4) (fail := t_07d0_c0) (e0 := 0x08) (e1 := 0x06)
    (x0 := 0x08) (x1 := 0x28) (r0 := 0x07) (r1 := 0xf3) (joinT := t_0828_c6) hfork hcd hv rfl rfl
    rfl (Or.inr ⟨rfl, rfl, hL⟩)

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

/-! ### `set_name`'s copy loops, forward -/

/-- **One of `set_name`'s store segments, forward**: from any base `d`, the set-up and the loop
store the words `ric_storeSeg` names, at a cost `c` fixed by `d` (at most three stores), and hand
the exit tree six more stack words; every run of the exit tree from gas above the `SSTORE`
sentry extends to one of the segment. -/
theorem rx_storeSeg (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {d : Devm} {S : List B256} {M : Mem} {s0 s1 sl cp e0 e1 x0 x1 r0 r1 : UInt8} {j k n sn : Nat}
    {exitT : SFunc} {src : Bytes}
    (hk : prog[k]? = some (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT))
    (hj : prog[j]? = some exitT) (hcase : (cp = 3 ∧ n = 2) ∨ (cp = 2 ∧ n = 1))
    (hS : S.length ≤ 16) (hs : M.size = 672) (hwf : Mem.Wf M)
    (hsn : (Bytes.toB256 [s0, s1]).toNat = sn) (hsn1 : 0x140 ≤ sn)
    (hsn2 : sn + 32 * (n + 1) ≤ 672)
    (hsrc : ∀ i, i ≤ n → (M.read (sn + 32 * i) 32).1 = src.sliceD (32 * i) 32 0)
    (hL : (Bytes.toB256 (src.sliceD 0 32 0)).toNat ≤ 32 * n) :
    ∃ (y1 y2 y3 y4 y5 y6 : B256) (d' : Devm) (M' : Mem) (c : Nat),
      c ≤ 489 + 3 * (gasColdSload + gasStorageSet) ∧
      Devm.getStor d' sevm.currentTarget = vyCopyStore (Devm.getStor d sevm.currentTarget)
        (Bytes.toB256 [sl]).toBytes.keccak src
        (min (n + 1) ((32 + (Bytes.toB256 (src.sliceD 0 32 0)).toNat) / 32 + 1)) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor d' a = Devm.getStor d a) ∧
      d'.logs = d.logs ∧ M'.size = 672 ∧ Mem.Wf M' ∧
      (∀ a len, 0x140 ≤ a → (M'.read a len).1 = (M.read a len).1) ∧
      ∀ G o, gCallStipend < G →
        SFunc.RunExact prog sevm (St d' (y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: S) M' G) exitT o →
        SFunc.RunExact prog sevm (St d S M (G + c))
          (vyStoreHead s0 s1 sl cp (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT)) o := by
  set base := (Bytes.toB256 [sl]).toBytes.keccak
  set L := (Bytes.toB256 (src.sliceD 0 32 0)).toNat with hLdef
  set srcB := Bytes.toB256 [s0, s1]
  have hLw : Bytes.toB256 (M.read sn 32).1 = Bytes.toB256 (src.sliceD 0 32 0) := by
    have := hsrc 0 (Nat.zero_le _); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this]
  set lp := Bytes.toB256 (M.read sn 32).1 + Bytes.toB256 [0x20]
  have hlp : lp.toNat = L + 32 := by
    show (Bytes.toB256 (M.read sn 32).1 + Bytes.toB256 [0x20]).toNat = _
    rw [hLw, B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by omega)]
  set cap := Bytes.toB256 [cp] + Nat.toB256 0
  set M1 := M.write 0xc0 (Bytes.toB256 [sl]).toBytes
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  set M2 := M1.write 0x120 (Nat.toB256 0).toBytes
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hsz : ∀ (N : Mem) (w : B256), N.size = 672 → (N.write 0x120 w.toBytes).size = 672 := by
    intro N w h; rw [Mem.size_write_of_le (by rw [B256.length_toBytes, h]; omega), h]
  have hs1 : M1.size = 672 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hs]; omega), hs]
  have hs2 : M2.size = 672 := hsz M1 _ hs1
  have hkeep : ∀ (N : Mem) (w : B256) (n' : Nat), Mem.Wf N → n' + 32 ≤ 0x140 →
      ∀ a len, 0x140 ≤ a → ((N.write n' w.toBytes).read a len).1 = (N.read a len).1 :=
    fun N w n' hN hn a len ha =>
      Mem.read_write_disjoint hN _ _ (Or.inl (by rw [B256.length_toBytes]; omega))
  have hk2 : ∀ a len, 0x140 ≤ a → (M2.read a len).1 = (M.read a len).1 := by
    intro a len ha
    rw [hkeep M1 _ _ hwf1 (by omega) a len ha, hkeep M _ _ hwf (by omega) a len ha]
  have hc2 : (M2.read 0x120 32).1 = (Nat.toB256 0).toBytes := Mem.read_write_word_of_wf hwf1 _ _
  set d1 := afterSstore sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1)
  set M3 := M2.write 0x120 (Nat.toB256 (0 + 1)).toBytes
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hs3 : M3.size = 672 := hsz M2 _ hs2
  have hk3 : ∀ a len, 0x140 ≤ a → (M3.read a len).1 = (M.read a len).1 := by
    intro a len ha; rw [hkeep M2 _ _ hwf2 (by omega) a len ha, hk2 a len ha]
  have hc3 : (M3.read 0x120 32).1 = (Nat.toB256 1).toBytes := Mem.read_write_word_of_wf hwf2 _ _
  set d2 := afterSstore sevm d1 (base + Nat.toB256 1) (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1)
  set M4 := M3.write 0x120 (Nat.toB256 (1 + 1)).toBytes
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hs4 : M4.size = 672 := hsz M3 _ hs3
  have hk4 : ∀ a len, 0x140 ≤ a → (M4.read a len).1 = (M.read a len).1 := by
    intro a len ha; rw [hkeep M3 _ _ hwf3 (by omega) a len ha, hk3 a len ha]
  have hc4 : (M4.read 0x120 32).1 = (Nat.toB256 2).toBytes := Mem.read_write_word_of_wf hwf3 _ _
  have hw0 : Bytes.toB256 (M2.read (sn + 32 * 0) 32).1 = Bytes.toB256 (src.sliceD (32 * 0) 32 0) := by
    rw [hk2 _ _ (by omega), hsrc 0 (Nat.zero_le _)]
  have hw1 : Bytes.toB256 (M3.read (sn + 32 * 1) 32).1 = Bytes.toB256 (src.sliceD (32 * 1) 32 0) := by
    rw [hk3 _ _ (by omega), hsrc 1 (by omega)]
  have hst2 : Devm.getStor d2 sevm.currentTarget =
      vyCopyStore (Devm.getStor d sevm.currentTarget) base src 2 := by
    simp only [d2, d1, afterSstore_getStor_self, hw0, hw1]; rfl
  have hot2 : ∀ a, a ≠ sevm.currentTarget → Devm.getStor d2 a = Devm.getStor d a := by
    intro a ha
    simp only [d2, d1]
    rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha)]
  have hlg2 : d2.logs = d.logs := by simp only [d2, d1, afterSstore_logs]
  have hb0 := sstoreCost_le sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1)
  have hb1 := sstoreCost_le sevm d1 (base + Nat.toB256 1) (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1)
  have hroom : ([srcB] ++ S).length + 12 < 1024 := by simp; omega
  have hne1 : cap ≠ Nat.toB256 (0 + 1) := by rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `name`
    by_cases hL32 : L < 32
    · refine ⟨cap, 0x120, lp, base, srcB, srcB, d2, M4,
        48 + 117 + sstoreCost sevm d1 (base + Nat.toB256 1)
          (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
          sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90,
        by omega, ?_, hot2, hlg2, hs4, hwf4, hk4, fun G o hG kk => ?_⟩
      · rw [hst2]; congr 1; omega
      rw [show G + (48 + 117 + sstoreCost sevm d1 (base + Nat.toB256 1)
          (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
          sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90) =
        G + 48 + 117 + sstoreCost sevm d1 (base + Nat.toB256 1)
          (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
          sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90
        by omega]
      refine rx_vyStoreHead (by omega) hs (by decide) (by decide) hwf hsn (by omega) (by omega) ?_
      refine rx_vyStoreStep hfork hstatic hroom (i := 0) (by omega) hne1 hs2 (by decide) (by decide)
        hsn (by omega) (by decide) hc2 (by omega) hk ?_
      refine rx_vyStoreStep hfork hstatic hroom (i := 1) (le_of_le_of_eq (by omega) hlp.symm)
        (by decide) hs3 (by decide) (by decide) hsn (by omega) (by decide) hc3 (by omega) hk ?_
      exact rx_vyStoreExit hroom (i := 2) (lt_of_eq_of_lt hlp (by omega)) (by decide) hs4 (by decide)
        (by decide) hc4 hj kk
    · have hw2 : Bytes.toB256 (M4.read (sn + 32 * 2) 32).1 =
          Bytes.toB256 (src.sliceD (32 * 2) 32 0) := by
        rw [hk4 _ _ (by omega), hsrc 2 le_rfl]
      have hb2 := sstoreCost_le sevm d2 (base + Nat.toB256 2)
        (Bytes.toB256 (M4.read (sn + 32 * 2) 32).1)
      refine ⟨cap, 0x120, lp, base, srcB, srcB,
        afterSstore sevm d2 (base + Nat.toB256 2) (Bytes.toB256 (M4.read (sn + 32 * 2) 32).1),
        M4.write 0x120 (Nat.toB256 (2 + 1)).toBytes,
        117 + sstoreCost sevm d2 (base + Nat.toB256 2) (Bytes.toB256 (M4.read (sn + 32 * 2) 32).1) +
          117 + sstoreCost sevm d1 (base + Nat.toB256 1)
          (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
          sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90,
        by omega, ?_, ?_, ?_, hsz M4 _ hs4, hwf4.write _ _, ?_, fun G o hG kk => ?_⟩
      · rw [afterSstore_getStor_self, hst2, hw2, show min (2 + 1) ((32 + L) / 32 + 1) = 3 by omega]
        rfl
      · intro a ha
        rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), hot2 a ha]
      · rw [afterSstore_logs, hlg2]
      · intro a len ha; rw [hkeep M4 _ _ hwf4 (by omega) a len ha, hk4 a len ha]
      rw [show G + (117 + sstoreCost sevm d2 (base + Nat.toB256 2)
          (Bytes.toB256 (M4.read (sn + 32 * 2) 32).1) + 117 + sstoreCost sevm d1 (base + Nat.toB256 1)
          (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
          sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90) =
        G + 117 + sstoreCost sevm d2 (base + Nat.toB256 2)
          (Bytes.toB256 (M4.read (sn + 32 * 2) 32).1) + 117 + sstoreCost sevm d1 (base + Nat.toB256 1)
          (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
          sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90
        by omega]
      refine rx_vyStoreHead (by omega) hs (by decide) (by decide) hwf hsn (by omega) (by omega) ?_
      refine rx_vyStoreStep hfork hstatic hroom (i := 0) (by omega) hne1 hs2 (by decide) (by decide)
        hsn (by omega) (by decide) hc2 (by omega) hk ?_
      refine rx_vyStoreStep hfork hstatic hroom (i := 1) (le_of_le_of_eq (by omega) hlp.symm)
        (by decide) hs3 (by decide) (by decide) hsn (by omega) (by decide) hc3 (by omega) hk ?_
      exact rx_vyStoreLast hfork hstatic hroom (i := 2) (le_of_le_of_eq (by omega) hlp.symm)
        (by decide) hs4 (by decide) (by decide) hsn (by omega) (by decide) hc4 hG kk
  · -- `symbol`
    refine ⟨cap, 0x120, lp, base, srcB, srcB, d2, M4,
      117 + sstoreCost sevm d1 (base + Nat.toB256 1) (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) +
        117 + sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90,
      by omega, ?_, hot2, hlg2, hs4, hwf4, hk4, fun G o hG kk => ?_⟩
    · rw [hst2, show min (1 + 1) ((32 + L) / 32 + 1) = 2 by omega]
    rw [show G + (117 + sstoreCost sevm d1 (base + Nat.toB256 1)
        (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
        sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90) =
      G + 117 + sstoreCost sevm d1 (base + Nat.toB256 1)
        (Bytes.toB256 (M3.read (sn + 32 * 1) 32).1) + 117 +
        sstoreCost sevm d (base + Nat.toB256 0) (Bytes.toB256 (M2.read (sn + 32 * 0) 32).1) + 90
      by omega]
    refine rx_vyStoreHead (by omega) hs (by decide) (by decide) hwf hsn (by omega) (by omega) ?_
    refine rx_vyStoreStep hfork hstatic hroom (i := 0) (by omega) hne1 hs2 (by decide) (by decide)
      hsn (by omega) (by decide) hc2 (by omega) hk ?_
    exact rx_vyStoreLast hfork hstatic hroom (i := 1) (le_of_le_of_eq (by omega) hlp.symm)
      (by decide) hs3 (by decide) (by decide) hsn (by omega) (by decide) hc3 hG kk

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

/-- `OwnerCallOk` with the answer's length a word: `RETURNDATASIZE` pushes the length modulo
`2^256`, so the frozen `OwnerCallOk` alone cannot rule out a wrapped length failing the
`RETURNDATASIZE > 31` check (see the note on `live_setName`). -/
def OwnerCallOkLt (sevm : Sevm) (b : Devm) (w : B256) (R Gc : Nat) : Prop :=
  ∀ (S : List B256) (M : Mem) (G : Nat), Gc ≤ G → G < 2 ^ 256 →
    (M.read 0x23c 4).1 = ownerCalldata →
    ∃ d out, Ninst.RunCompiled sevm
        (St (afterSload sevm b vyMinterSlot) (Nat.toB256 G ::
          b.getStorVal sevm.currentTarget vyMinterSlot :: 0x23c :: 4 :: 0x280 :: 0x20 :: S) M G)
        (.exec .staticcall) d ∧
      StaticCallPost (afterSload sevm b vyMinterSlot) d S M 0x23c 4 0x280 0x20 1 out ∧
      32 ≤ out.length ∧ Bytes.toB256 (out.take 32) = w ∧ R ≤ d.gasLeft ∧ out.length < 2 ^ 256

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

namespace Blanc.Lift.Curve3Crv

open Jaune

/-- **`set_name`, forward**, under `OwnerCallOkLt` (the owner's answer is shorter than
`2^256` bytes). -/
theorem live_setName_lt {sevm : Sevm} {b : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw}
    (hr : rawSetName sevm (Devm.getStor b sevm.currentTarget) (some sevm.caller.toB256) =
      some r) :
    ∃ R P, ∀ Gc, OwnerCallOkLt sevm b sevm.caller.toB256 R Gc → ∀ G, Gc + P ≤ G → G < 2 ^ 256 →
      ∃ post, SFunc.RunExact prog sevm (entrySt sevm b G) t_00f1_c0 (.halted post) ∧
        Lands sevm b post r := by
  unfold rawSetName at hr
  dsimp only at hr
  split_ifs at hr with h
  cases hr
  obtain ⟨hv, hL0, hL1, -⟩ := h
  set sc := sloadCost sevm b vyMinterSlot
  refine ⟨2 * (489 + 3 * (gasColdSload + gasStorageSet)) + 90 + gCallStipend + 1, 216 + sc,
    fun Gc hok G hG hG' => ?_⟩
  obtain ⟨Gcall, rfl⟩ : ∃ G', G = G' + (216 + sc) := ⟨G - (216 + sc), by omega⟩
  -- numerals and memory before the call
  have n320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have n96 : (Bytes.toB256 [0x60]).toNat = 96 := by decide
  have n448 : (Bytes.toB256 [0x01, 0xc0]).toNat = 448 := by decide
  have n64 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have n544 : (Bytes.toB256 [0x02, 0x20]).toNat = 544 := by decide
  have n640 : (Bytes.toB256 [0x02, 0x80]).toNat = 640 := by decide
  have hM0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have hr0 : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0)) (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  set s0B := Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x04])
  set s1B := Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x24])
  have hs0 : s0B = Sevm.argWord sevm 0 + 4 := by
    show Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x04]) = _
    rw [B256.add_comm, show Bytes.toB256 [0x04] = 4 by decide]; rfl
  have hs1 : s1B = Sevm.argWord sevm 1 + 4 := by
    show Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x24]) = _
    rw [B256.add_comm, show Bytes.toB256 [0x04] = 4 by decide]
    congr 1
  rw [← hs0] at hL0
  rw [← hs1] at hL1
  set src0 := sevm.data.sliceD s0B.toNat 96 0
  set src1 := sevm.data.sliceD s1B.toNat 64 0
  set selw := Bytes.toB256 [0x8d, 0xa5, 0xcb, 0x5b]
  set M0 := vyMem Mem.empty (Sevm.dataWord sevm 0)
  set M1 := M0.write 320 src0
  set M2 := M1.write 448 src1
  set M3 := M2.write 544 selw.toBytes
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hs1' : M1.size = 416 := by
    rw [Mem.size_write_of_length (List.length_sliceD _ _ _ _) (by decide), hM0]; rfl
  have hs2 : M2.size = 512 := by
    rw [Mem.size_write_of_length (List.length_sliceD _ _ _ _) (by decide), hs1']; rfl
  have hs3 : M3.size = 576 := by
    rw [Mem.size_write_of_length (B256.length_toBytes _) (by decide), hs2]; rfl
  have hin : (M3.read 0x23c 4).1 = ownerCalldata := by
    rw [((Mem.reads_data M2).write hwf2 544 selw.toBytes).read,
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  -- the owner's answer
  obtain ⟨d, out, hcall, hpost, hlen, hword, hR, hlt⟩ :=
    hok [sevm.caller.toB256] M3 Gcall (by omega) (by omega) hin
  set M3e := M3.extends [(572, 4), (640, 32)]
  set M4 := M3e.write 640 (out.take 32)
  have hwf3e : Mem.Wf M3e := Mem.Wf.extends _ hwf3
  have hwf4 : Mem.Wf M4 := hwf3e.write _ _
  have hs3e : M3e.size = 672 := by
    show memExtsSize M3.size _ = _
    rw [hs3]; rfl
  have hs4 : M4.size = 672 := by
    rw [Mem.size_write_of_le (by rw [hs3e, List.length_take]; omega), hs3e]
  have hr4 : Mem.Reads M4 (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (vyImg [] (Sevm.dataWord sevm 0)) 320 src0) 448 src1) 544 selw.toBytes) 640 (out.take 32)) :=
    (Mem.Reads.extends _ (((hr0.write hwf0 _ _).write hwf1 _ _).write hwf2 _ _)).write hwf3e _ _
  have hw640 : (M4.read 640 32).1 = out.take 32 := by
    rw [hr4.read]
    have h := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (vyImg [] (Sevm.dataWord sevm 0)) 320 src0) 448 src1) 544 selw.toBytes) (out.take 32) 640
    rwa [List.length_take, Nat.min_eq_left hlen] at h
  -- the two copy loops, from the call's world
  have hL0w : Bytes.toB256 (src0.sliceD 0 32 0) = Sevm.dataWord sevm s0B := by
    rw [Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide), Nat.add_zero]; rfl
  have hL1w : Bytes.toB256 (src1.sliceD 0 32 0) = Sevm.dataWord sevm s1B := by
    rw [Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide), Nat.add_zero]; rfl
  have hsrc0 : ∀ i, i ≤ 2 → (M4.read (320 + 32 * i) 32).1 = src0.sliceD (32 * i) 32 0 := by
    intro i hi
    rw [hr4.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_sliceD]; omega),
      Nat.add_sub_cancel_left]
  obtain ⟨y1, y2, y3, y4, y5, y6, d', M', c1, hc1, hst1, hot1, hlg1, hs', hwf', hk', hrun1⟩ :=
    rx_storeSeg (s0 := 0x01) (s1 := 0x40) (sl := 0x00) (cp := 0x03) (e0 := 0x01) (e1 := 0xad)
      (x0 := 0x01) (x1 := 0xcf) (r0 := 0x01) (r1 := 0x9a) (j := 1) (k := 8) (n := 2)
      (exitT := t_01cf_c1) (src := src0) (d := d) (S := []) hfork hstatic rfl rfl
      (Or.inl ⟨rfl, rfl⟩) (by simp) hs4 hwf4 n320 (by decide) (by decide) hsrc0
      (by rw [hL0w]; omega)
  have hsrc1 : ∀ i, i ≤ 1 → (M'.read (448 + 32 * i) 32).1 = src1.sliceD (32 * i) 32 0 := by
    intro i hi
    rw [hk' _ _ (by omega), hr4.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_sliceD]; omega),
      Nat.add_sub_cancel_left]
  obtain ⟨z1, z2, z3, z4, z5, z6, d'', M'', c2, hc2, hst2, hot2, hlg2, -, -, -, hrun2⟩ :=
    rx_storeSeg (s0 := 0x01) (s1 := 0xc0) (sl := 0x01) (cp := 0x02) (e0 := 0x02) (e1 := 0x07)
      (x0 := 0x02) (x1 := 0x29) (r0 := 0x01) (r1 := 0xf4) (j := 2) (k := 11) (n := 1)
      (exitT := t_0229_c2) (src := src1) (d := d') (S := []) hfork hstatic rfl rfl
      (Or.inr ⟨rfl, rfl⟩) (by simp) hs' hwf' n448 (by decide) (by decide) hsrc1
      (by rw [hL1w]; omega)
  set Gf := d.gasLeft - (13 + c2 + 13 + c1 + 64)
  have hGf : d.gasLeft = Gf + 13 + c2 + 13 + c1 + 64 := by omega
  have hGf' : gCallStipend < Gf := by omega
  refine ⟨St d'' [] M'' Gf, ?_, ?_⟩
  · have hgt0 : B256.gtCheck (Sevm.dataWord sevm s0B) (Bytes.toB256 [0x40]) = 0 := by
      rw [B256.gtCheck, ite_eq_right_iff]
      intro h
      rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, n64] at h
      omega
    have hgt1 : B256.gtCheck (Sevm.dataWord sevm s1B) (Bytes.toB256 [0x20]) = 0 := by
      rw [B256.gtCheck, ite_eq_right_iff]
      intro h
      rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x20]).toNat = 32 by decide] at h
      omega
    unfold entrySt
    rw [show Gcall + (216 + sc) = Gcall + 2 + sc + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 3 + 2 + 1 + 10 +
      3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 18 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 +
      3 + 3 + 3 + 3 + 33 + 3 + 3 + 3 + 3 + 3 + 3 + 19 by omega]
    refine rx_vyNonpayable (h := 0x00) (l := 0xfb) (fail := t_00f7_c0) hv (by simp) ?_
    -- `name`'s bytes and guard
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_add (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldatacopy (c := 33) ?_ (by rw [n320, n96]) ?_
    · rw [n320, n96, St.extCost_eq hM0]; decide
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_add (by simp) ?_
    refine rx_calldataload (by simp) ?_
    refine rx_gt hgt0 (by simp) ?_
    refine rx_iszero (v := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    -- `symbol`'s bytes and guard
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_add (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldatacopy (c := 18) ?_ (by rw [n448, n64]) ?_
    · rw [n448, n64, St.extCost_eq hs1']; decide
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_add (by simp) ?_
    refine rx_calldataload (by simp) ?_
    refine rx_gt hgt1 (by simp) ?_
    refine rx_iszero (v := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    -- the owner call
    refine rx_caller (by simp) ?_
    refine rx_push (w := 0x20) (by decide) (by simp) ?_
    refine rx_push (w := 0x280) (by decide) (by simp) ?_
    refine rx_push (w := 4) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 9) ?_ (by rw [n544]) ?_
    · rw [n544, St.extCost_eq hs2]; decide
    refine rx_push (w := 0x23c) (by decide) (by simp) ?_
    refine rx_push (w := vyMinterSlot) (by decide) (by simp) ?_
    refine rx_sload_sel hfork (by show 5 < 1024; decide) ?_
    refine rx_gas (by show 6 < 1024; decide) ?_
    refine rx_staticcall hfork hcall ?_
    intro flag out' hp' _
    have hfl : flag = 1 := by
      have := hp'.stack.symm.trans hpost.stack
      exact (List.cons.inj this).1
    have hout : out' = out := hp'.returnData.symm.trans hpost.returnData
    rw [hfl, hout, show (0x23c : B256).toNat = 572 by decide, show (4 : B256).toNat = 4 by decide,
      show (0x280 : B256).toNat = 640 by decide, show (0x20 : B256).toNat = 32 by decide, hGf]
    -- the checks
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    refine rx_push rfl (by simp) ?_
    refine rx_returndatasize (by simp) ?_
    rw [hpost.returnData]
    refine rx_gt (v := 1) ?_ (by simp) ?_
    · rw [B256.gtCheck, ite_eq_left_iff]
      intro h
      exact absurd (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hlt,
        show (Bytes.toB256 [0x1f]).toNat = 31 by decide]; omega) h
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    refine rx_push rfl (by simp) ?_
    refine rx_pop ?_
    refine rx_push rfl (by simp) ?_
    refine rx_mload (c := 3) (v := Bytes.toB256 (out.take 32)) ?_ (by rw [n640, hw640])
      (by rw [n640]; exact read_covered hs4 (by decide) (by decide)) (by simp) ?_
    · rw [n640, St, Devm.extCost_zero_of_le (by rw [hs4]) (by rw [hs4])]; rfl
    refine rx_eq (v := 1) (by simp [B256.eqCheck, hword]) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    -- the two loops and joins
    refine hrun1 _ _ (by omega) ?_
    unfold t_01cf_c1
    refine rx_dest (rx_pop (rx_pop (rx_pop (rx_pop (rx_pop (rx_pop ?_))))))
    refine hrun2 _ _ (by omega) ?_
    unfold t_0229_c2
    exact rx_dest (rx_pop (rx_pop (rx_pop (rx_pop (rx_pop (rx_pop (.last rfl)))))))
  · have hnb : (Bytes.toB256 [0x00]).toBytes.keccak = vyNameBase := by
      rw [show Bytes.toB256 [0x00] = 0 by decide]; rfl
    have hsb : (Bytes.toB256 [0x01]).toBytes.keccak = vySymbolBase := by
      rw [show Bytes.toB256 [0x01] = 1 by decide]; rfl
    have hd : ∀ a, Devm.getStor d a = Devm.getStor b a := by
      intro a; rw [hpost.stor a, afterSload_getStor]
    refine ⟨?_, fun a ha => ?_, ?_, fun o ho => by cases ho⟩
    · show Devm.getStor d'' _ = _
      rw [hst2, hst1, hd, hnb, hsb, hL0w, hL1w, ← hs0, ← hs1]
    · show Devm.getStor d'' _ = _
      rw [hot2 a ha, hot1 a ha, hd]
    · show d''.logs = _
      rw [hlg2, hlg1, hpost.logs, afterSload_logs, List.append_nil]

end Blanc.Lift.Curve3Crv
