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
/-- The shared join-entry-3 tail of `live_transferFrom`: the event and `return(1)`, forward from
an arbitrary base state agreeing with `b` outside `sevm.currentTarget` and sharing `b`'s logs.
Its own declaration (proven once, with its own heartbeat budget) since both the `spend` and
minter arms need it and inlining a full copy in each pushed each arm's elaboration past the
default 200000-heartbeat limit. -/
private theorem live_transferFrom_tail (hstatic : sevm.isStatic = false) (f d v : B256)
    (hf0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = f)
    (hd1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = d)
    (hv2 : Sevm.dataWord sevm (Bytes.toB256 [0x44]) = v)
    (h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320)
    (h32 : (Bytes.toB256 [0x20]).toNat = 32)
    (h0 : (Bytes.toB256 [0x00]).toNat = 0) :
    ∀ (b' : Devm) (M' : Mem) (stf : Stor), Mem.Wf M' → M'.size = 256 →
      Devm.getStor b' sevm.currentTarget = stf →
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor b a) →
      b'.logs = b.logs → ∀ G, gCallStipend < G → ∃ post,
        SFunc.RunExact prog sevm (St b' [] M' (G + 1814)) t_045b_c3 (.halted post) ∧
          post.gasLeft = G ∧ Lands sevm b post
            (stf, [⟨sevm.currentTarget, [transferTopic, f, d], v.toBytes⟩],
              some (1 : B256).toBytes) := by
  intro b' M' stf hwf hMn hself hother hlogs G hG
  set N1 := M'.write 320 v.toBytes with hN1_def
  have hN1 : N1.size = 352 := by simp only [hN1_def, Mem.size_write_word_at, hMn]; decide
  have hwfN1 : Mem.Wf N1 := hwf.write _ _
  set b4 := b'.addLog (⟨sevm.currentTarget, [transferTopic, f, d], v.toBytes⟩ : Log)
    with hb4_def
  set N2 := N1.write 0 (1 : B256).toBytes with hN2_def
  refine ⟨((St b4 [] N2 G).memRead 0 32).2.withOutput (1 : B256).toBytes, ?_, rfl, ?_⟩
  · unfold t_045b_c3
    refine rx_dest ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hv2]
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 12) ?_ (M' := N1) (by rw [h320]) ?_
    · rw [h320, St.extCost_eq hMn]; decide
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd1]
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hf0]
    refine rx_push (w := transferTopic) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_log3 (c := 1756) (data := v.toBytes) hstatic ?_ ?_ ?_ ?_
    · rw [h320, h32, St, Devm.extCost_zero_of_le (by rw [hN1]) (by rw [hN1])]; decide
    · rw [h320, h32]; exact Mem.read_write_word_of_wf hwf 320 v
    · rw [h320, h32]; exact read_covered hN1 (by decide) (by decide)
    refine rx_push (w := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_mstore (c := 3) ?_ (M' := N2) (by rw [h0]) ?_
    · rw [h0, St, Devm.extCost_zero_of_le (by rw [hN1]) (by rw [hN1]; omega)]; rfl
    refine rx_push rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_return ?_ ?_
    · have hN2 : N2.size = 352 := by simp only [hN2_def, Mem.size_write_word_at, hN1]; decide
      rw [h0, h32, St, Devm.extCost_zero_of_le (by rw [hN2]) (by rw [hN2]; omega)]
    · rw [h0, h32]; exact Mem.read_write_word_of_wf hwfN1 0 1
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩
    · rw [getStor_St_return, getStor_addLog, hself]
    · rw [getStor_St_return, getStor_addLog, hother a ha]
    · rw [logs_St_return, logs_addLog, hlogs]
    · cases ho
      exact output_St_return _ _ _ _ _ _ _

/-- The `spend` (non-minter, allowance-debited) arm of `live_transferFrom`, its own declaration
so its proof gets a fresh elaborator heartbeat budget: the shared preamble plus both walks in one
declaration approached the default 200000-heartbeat limit (mirrors `refine_transferFrom_spend` in
`Refine.lean`). Takes the raw `spend` condition directly since the preamble that would otherwise
name it hasn't been introduced yet. -/
private theorem live_transferFrom_spend (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw} (hr : rawTransferFrom sevm stor₀ = some r)
    (hspend0 : (((Devm.getStor b sevm.currentTarget).set (mapSlot 3 (Sevm.argWord sevm 0))
          ((Devm.getStor b sevm.currentTarget).get (mapSlot 3 (Sevm.argWord sevm 0)) -
            Sevm.argWord sevm 2)).set (mapSlot 3 (Sevm.argWord sevm 1))
        (((Devm.getStor b sevm.currentTarget).set (mapSlot 3 (Sevm.argWord sevm 0))
              ((Devm.getStor b sevm.currentTarget).get (mapSlot 3 (Sevm.argWord sevm 0)) -
                Sevm.argWord sevm 2)).get (mapSlot 3 (Sevm.argWord sevm 1)) +
          Sevm.argWord sevm 2)).get vyMinterSlot ≠ sevm.caller.toB256) :
    BodyLive sevm b t_0390_c0 r := by
  simp only [rawTransferFrom] at hr
  split_ifs at hr with hg
  obtain ⟨hv, hfr, hdr, hle, hnof, hspendarrow⟩ := hg
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have h3 : Bytes.toB256 [0x03] = 3 := by decide
  have h4 : Bytes.toB256 [0x04] = 4 := by decide
  have h6 : Bytes.toB256 [0x06] = vyMinterSlot := by decide
  have hf0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  have hd1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hv2 : Sevm.dataWord sevm (Bytes.toB256 [0x44]) = Sevm.argWord sevm 2 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  set f := Sevm.argWord sevm 0 with hf_def
  set d := Sevm.argWord sevm 1 with hd_def
  set v := Sevm.argWord sevm 2 with hv_def
  set s1 := mapSlot 3 f with hs1_def
  set x := b.getStorVal sevm.currentTarget s1 with hx_def
  set b2 := afterSstore sevm (afterSload sevm b s1) s1 (x - v) with hb2_def
  set s2 := mapSlot 3 d with hs2_def
  set y := b2.getStorVal sevm.currentTarget s2 with hy_def
  set b3 := afterSstore sevm (afterSload sevm b2 s2) s2 (y + v) with hb3_def
  have hx_eq : x = (Devm.getStor b sevm.currentTarget).get s1 := rfl
  have hy_eq : y = ((Devm.getStor b sevm.currentTarget).set s1 (x - v)).get s2 := by
    rw [hy_def, hb2_def, getStorVal_afterStore]
  have hw_eq : b3.getStorVal sevm.currentTarget vyMinterSlot =
      (((Devm.getStor b sevm.currentTarget).set s1
          ((Devm.getStor b sevm.currentTarget).get s1 - v)).set s2
        (((Devm.getStor b sevm.currentTarget).set s1
          ((Devm.getStor b sevm.currentTarget).get s1 - v)).get s2 + v)).get vyMinterSlot := by
    rw [hb3_def, getStorVal_afterStore, hb2_def, getStor_afterStore, hy_eq, hx_eq]
  set M1 := ((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 224 f.toBytes).write 192
    (3 : B256).toBytes with hM1_def
  have hM1 : M1.size = 256 := by simp only [hM1_def, Mem.size_write_word_at, hM]; decide
  set M2 := (M1.write 224 d.toBytes).write 192 (3 : B256).toBytes with hM2_def
  have hM2 : M2.size = 256 := by simp only [hM2_def, Mem.size_write_word_at, hM1]; decide
  have hwf2 : Mem.Wf M2 := ((((hwf0.write _ _).write _ _).write _ _).write _ _)
  -- the shared tail (join entry 3): the event and `return(1)`, forward, from any base
  have tail := live_transferFrom_tail (b := b) hstatic f d v hf0 hd1 hv2 h320 h32 h0
  -- the allowance is spent
  have hr' := (Option.some.inj hr).symm
  subst hr'
  set s3 := mapSlot (mapSlot 4 f) sevm.caller.toB256 with hs3_def
  -- the minter read warms `vyMinterSlot`: the allowance block runs over `b3m`, not `b3`
  set b3m := afterSload sevm b3 vyMinterSlot with hb3m_def
  set z := b3m.getStorVal sevm.currentTarget s3 with hz_def
  have hz_eq : z = (((Devm.getStor b sevm.currentTarget).set s1
      ((Devm.getStor b sevm.currentTarget).get s1 - v)).set s2
      (((Devm.getStor b sevm.currentTarget).set s1
        ((Devm.getStor b sevm.currentTarget).get s1 - v)).get s2 + v)).get s3 := by
    rw [hz_def, hb3m_def, getStorVal_afterSload, hb3_def, getStorVal_afterStore, hb2_def, getStor_afterStore, hy_eq, hx_eq]
  have hzle : v ≤ z := by rw [hz_eq]; exact hspendarrow hspend0
  set b4 := afterSstore sevm (afterSload sevm b3m s3) s3 (z - v) with hb4_def
  -- the allowance slot's two `vySlot`s leave their own scratch words in memory
  set M3 := (((M2.write 224 f.toBytes).write 192 (4 : B256).toBytes).write 224
    sevm.caller.toB256.toBytes).write 192 (mapSlot 4 f).toBytes with hM3_def
  have hM3 : M3.size = 256 := by simp only [hM3_def, Mem.size_write_word_at, hM2]; decide
  have hwf3 : Mem.Wf M3 := ((((hwf2.write _ _).write _ _).write _ _).write _ _)
  refine ⟨1814 +
    (2 + sstoreCost sevm (afterSload sevm b3m s3) s3 (z - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
      10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b3m s3 + 3) +
    (42 + 3 + 3 + 3 + 3 + 3 + 3) + 2 + (42 + 3 + 3 + 3 + 3 + 3 + 3) + 3 + 3 + 3 +
    10 + 3 + 3 + 3 + 2 + sloadCost sevm b3 vyMinterSlot + 3 +
    (2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
      10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3) +
    (42 + 3 + 3 + 3 + 3 + 3 + 3) + 3 + 3 + 3 +
    (2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
      10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3) +
    (42 + 3 + 3 + 3 + 3 + 9 + 3) + 3 + 3 + 3 + 34 + 34 + 19, fun G hG => ?_⟩
  obtain ⟨post, hrun, hgas, hland⟩ := tail b4 M3
    (((Devm.getStor b sevm.currentTarget).set s1
        ((Devm.getStor b sevm.currentTarget).get s1 - v)).set s2
      (((Devm.getStor b sevm.currentTarget).set s1
          ((Devm.getStor b sevm.currentTarget).get s1 - v)).get s2 + v)|>.set s3
      ((((Devm.getStor b sevm.currentTarget).set s1
            ((Devm.getStor b sevm.currentTarget).get s1 - v)).set s2
          (((Devm.getStor b sevm.currentTarget).set s1
              ((Devm.getStor b sevm.currentTarget).get s1 - v)).get s2 + v)).get s3 - v))
    hwf3 hM3
    (by rw [hb4_def, getStor_afterStore, hb3m_def, afterSload_getStor, hb3_def, getStor_afterStore, hb2_def,
        getStor_afterStore, hy_eq, hx_eq, hz_eq])
    (fun a ha => by
      rw [hb4_def, getStor_afterStore_ne ha, hb3m_def, afterSload_getStor, hb3_def, getStor_afterStore_ne ha, hb2_def,
        getStor_afterStore_ne ha])
    (by rw [hb4_def, logs_afterStore, hb3m_def, afterSload_logs, hb3_def, logs_afterStore, hb2_def, logs_afterStore])
    G hG
  refine ⟨post, ?_, hgas, hland⟩
  unfold entrySt
  rw [show G + (1814 +
      (2 + sstoreCost sevm (afterSload sevm b3m s3) s3 (z - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b3m s3 + 3) +
      (42 + 3 + 3 + 3 + 3 + 3 + 3) + 2 + (42 + 3 + 3 + 3 + 3 + 3 + 3) + 3 + 3 + 3 +
      10 + 3 + 3 + 3 + 2 + sloadCost sevm b3 vyMinterSlot + 3 +
      (2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 +
        1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3) +
      (42 + 3 + 3 + 3 + 3 + 3 + 3) + 3 + 3 + 3 +
      (2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3) +
      (42 + 3 + 3 + 3 + 3 + 9 + 3) + 3 + 3 + 3 + 34 + 34 + 19) =
    G + 1814 +
      2 + sstoreCost sevm (afterSload sevm b3m s3) s3 (z - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b3m s3 + 3 +
      42 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
      10 + 3 + 3 + 3 + 2 + sloadCost sevm b3 vyMinterSlot + 3 +
      2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 +
        1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 +
      42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
      2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3 +
      42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 34 + 34 + 19 by omega]
  refine rx_vyNonpayable (h := 0x03) (l := 0x9a) (fail := t_0396_c0) hv (by decide) ?_
  refine rx_vyAddrArg (p := 0x04) (h := 0x03) (l := 0xab) (fail := t_03a7_c0)
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) (by rw [hf0]; exact hfr) (by simp) ?_
  refine rx_vyAddrArg (p := 0x24) (h := 0x03) (l := 0xbd) (fail := t_03b9_c0)
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) (by rw [hd1]; exact hdr) (by simp) ?_
  refine rx_push (w := 3) h3 (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [hf0]
  refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp) ?_
  refine rx_vySubStore (p := 0x44) (h := 0x03) (l := 0xe0) (fail := t_03dc_c0) hfork hstatic
    (by rw [hv2]; exact hle) (by omega) (by simp) ?_
  refine rx_push (w := 3) h3 (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [hd1]
  refine rx_vySlot (c1 := 3) hM1 (by omega) (by decide) (by decide) (by simp) ?_
  refine rx_vyAddStore (p := 0x44) (h := 0x04) (l := 0x0e) (fail := t_040a_c0) hfork hstatic
    (by rw [hv2, ← hs1_def, ← hx_def, ← hb2_def, ← hs2_def, ← hy_def, hy_eq, hx_eq]
        exact hnof) (by omega) (by simp) ?_
  rw [hv2, ← hs1_def, ← hx_def, ← hb2_def, ← hs2_def, ← hy_def]
  refine rx_push (w := 6) h6 (by simp) ?_
  refine rx_sload_sel hfork (by simp) ?_
  rw [← hb3_def]
  refine rx_caller (by simp) ?_
  refine rx_xor (v := sevm.caller.toB256 ^^^ b3.getStorVal sevm.currentTarget vyMinterSlot) rfl
    (by simp) ?_
  refine rx_iszero (v := 0) (by
    have hne : sevm.caller.toB256 ^^^ b3.getStorVal sevm.currentTarget vyMinterSlot ≠ 0 := by
      simp only [ne_eq, B256.xor_eq_zero_iff]
      rw [hw_eq]
      exact fun hc => hspend0 hc.symm
    simp [B256.eqCheck, hne]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branchTo_zero ?_
  rw [show afterSload sevm b3 6 = b3m from rfl]
  unfold t_0423_c0
  refine rx_push (w := 4) h4 (by simp) ?_
  refine rx_push (w := 4) h4 (by simp) ?_
  refine rx_calldataload (by simp) ?_
  rw [show Sevm.dataWord sevm (4 : B256) = f by rw [← h4]; exact hf0]
  refine rx_vySlot (c1 := 3) hM2 (by omega) (by decide) (by decide) (by simp) ?_
  refine rx_caller (by simp) ?_
  refine rx_vySlot (c1 := 3)
    (show ((M2.write 224 f.toBytes).write 192 (4 : B256).toBytes).size = 256 by
      simp only [Mem.size_write_word_at, hM2]; decide)
    (by omega) (by decide) (by decide) (by simp) ?_
  refine rx_vySubStore (p := 0x44) (h := 0x04) (l := 0x50) (fail := t_044c_c0) hfork hstatic
    (by rw [hv2]; exact hzle) (by omega) (by simp) ?_
  rw [hv2]
  exact hrun

/-- `transferFrom`: forwards of `safeTransferFrom`, the minter branch decided by `rawTransferFrom`'s
`spend`: `rx_branchTo_succ` into entry 3 when the caller is the minter, the allowance block
otherwise (`live_transferFrom_spend`, its own declaration for the heartbeat budget); the shared
tail proved once over an arbitrary base. -/
theorem live_transferFrom (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw} (hr : rawTransferFrom sevm stor₀ = some r) :
    BodyLive sevm b t_0390_c0 r := by
  have hr0 := hr
  simp only [rawTransferFrom] at hr
  split_ifs at hr with hg hspend0
  · exact live_transferFrom_spend hfork hstatic hr0 hspend0
  · -- ¬ spend (the caller is the minter)
    obtain ⟨hv, hfr, hdr, hle, hnof, hspendarrow⟩ := hg
    have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
    have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
    have h3 : Bytes.toB256 [0x03] = 3 := by decide
    have h4 : Bytes.toB256 [0x04] = 4 := by decide
    have h6 : Bytes.toB256 [0x06] = vyMinterSlot := by decide
    have hf0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
    have hd1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
      show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
      congr 1
    have hv2 : Sevm.dataWord sevm (Bytes.toB256 [0x44]) = Sevm.argWord sevm 2 := by
      show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
      congr 1
    have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
    have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
    have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
    set f := Sevm.argWord sevm 0 with hf_def
    set d := Sevm.argWord sevm 1 with hd_def
    set v := Sevm.argWord sevm 2 with hv_def
    set s1 := mapSlot 3 f with hs1_def
    set x := b.getStorVal sevm.currentTarget s1 with hx_def
    set b2 := afterSstore sevm (afterSload sevm b s1) s1 (x - v) with hb2_def
    set s2 := mapSlot 3 d with hs2_def
    set y := b2.getStorVal sevm.currentTarget s2 with hy_def
    set b3 := afterSstore sevm (afterSload sevm b2 s2) s2 (y + v) with hb3_def
    have hx_eq : x = (Devm.getStor b sevm.currentTarget).get s1 := rfl
    have hy_eq : y = ((Devm.getStor b sevm.currentTarget).set s1 (x - v)).get s2 := by
      rw [hy_def, hb2_def, getStorVal_afterStore]
    set M1 := ((vyMem Mem.empty (Sevm.dataWord sevm 0)).write 224 f.toBytes).write 192
      (3 : B256).toBytes with hM1_def
    have hM1 : M1.size = 256 := by simp only [hM1_def, Mem.size_write_word_at, hM]; decide
    set M2 := (M1.write 224 d.toBytes).write 192 (3 : B256).toBytes with hM2_def
    have hM2 : M2.size = 256 := by simp only [hM2_def, Mem.size_write_word_at, hM1]; decide
    have hwf2 : Mem.Wf M2 := ((((hwf0.write _ _).write _ _).write _ _).write _ _)
    -- the shared tail (join entry 3): the event and `return(1)`, forward, from any base
    have tail := live_transferFrom_tail (b := b) hstatic f d v hf0 hd1 hv2 h320 h32 h0
    have hr' := (Option.some.inj hr).symm
    subst hr'
    have hb3_minter : b3.getStorVal sevm.currentTarget vyMinterSlot = sevm.caller.toB256 := by
      rw [hb3_def, getStorVal_afterStore, hb2_def, getStor_afterStore, hy_eq, hx_eq]
      by_contra hc
      exact hspend0 hc
    have hb3_minter' : b3.getStorVal sevm.currentTarget 6 = sevm.caller.toB256 := hb3_minter
    refine ⟨1814 + 10 + 3 + 3 + 3 + 2 + sloadCost sevm b3 vyMinterSlot + 3 +
      (2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3) +
      (42 + 3 + 3 + 3 + 3 + 3 + 3) + 3 + 3 + 3 +
      (2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3) +
      (42 + 3 + 3 + 3 + 3 + 9 + 3) + 3 + 3 + 3 + 34 + 34 + 19, fun G hG => ?_⟩
    obtain ⟨post, hrun, hgas, hland⟩ := tail (afterSload sevm b3 vyMinterSlot) M2
      (((Devm.getStor b sevm.currentTarget).set s1 ((Devm.getStor b sevm.currentTarget).get s1 - v)).set s2
        (((Devm.getStor b sevm.currentTarget).set s1 ((Devm.getStor b sevm.currentTarget).get s1 - v)).get s2 +
          v)) hwf2 hM2
      (by rw [afterSload_getStor, hb3_def, getStor_afterStore, hb2_def, getStor_afterStore, hy_eq, hx_eq])
      (fun a ha => by
        rw [afterSload_getStor, hb3_def, getStor_afterStore_ne ha, hb2_def, getStor_afterStore_ne ha])
      (by rw [afterSload_logs, hb3_def, logs_afterStore, hb2_def, logs_afterStore]) G hG
    refine ⟨post, ?_, hgas, hland⟩
    unfold entrySt
    rw [show G + (1814 + 10 + 3 + 3 + 3 + 2 + sloadCost sevm b3 vyMinterSlot + 3 +
        (2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
          10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3) +
        (42 + 3 + 3 + 3 + 3 + 3 + 3) + 3 + 3 + 3 +
        (2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
          10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3) +
        (42 + 3 + 3 + 3 + 3 + 9 + 3) + 3 + 3 + 3 + 34 + 34 + 19) =
      G + 1814 + 10 + 3 + 3 + 3 + 2 + sloadCost sevm b3 vyMinterSlot + 3 +
        2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
          10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 +
        42 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
        2 + sstoreCost sevm (afterSload sevm b s1) s1 (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 +
          10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b s1 + 3 +
        42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 34 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x03) (l := 0x9a) (fail := t_0396_c0) hv (by decide) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x03) (l := 0xab) (fail := t_03a7_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
      (by rw [hM]; omega) (by rw [hf0]; exact hfr) (by simp) ?_
    refine rx_vyAddrArg (p := 0x24) (h := 0x03) (l := 0xbd) (fail := t_03b9_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
      (by rw [hM]; omega) (by rw [hd1]; exact hdr) (by simp) ?_
    refine rx_push (w := 3) h3 (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hf0]
    refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_vySubStore (p := 0x44) (h := 0x03) (l := 0xe0) (fail := t_03dc_c0) hfork hstatic
      (by rw [hv2]; exact hle) (by omega) (by simp) ?_
    refine rx_push (w := 3) h3 (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hd1]
    refine rx_vySlot (c1 := 3) hM1 (by omega) (by decide) (by decide) (by simp) ?_
    refine rx_vyAddStore (p := 0x44) (h := 0x04) (l := 0x0e) (fail := t_040a_c0) hfork hstatic
      (by rw [hv2, ← hs1_def, ← hx_def, ← hb2_def, ← hs2_def, ← hy_def, hy_eq, hx_eq]
          exact hnof) (by omega) (by simp) ?_
    rw [hv2, ← hs1_def, ← hx_def, ← hb2_def, ← hs2_def, ← hy_def]
    refine rx_push (w := 6) h6 (by simp) ?_
    refine rx_sload_sel hfork (by simp) ?_
    rw [← hb3_def]
    refine rx_caller (by simp) ?_
    refine rx_xor (v := 0) (by rw [hb3_minter', B256.xor_eq_zero_iff]) (by simp) ?_
    refine rx_iszero (v := 1) (by decide) (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_branchTo_succ (j := 3) (by decide) rfl ?_
    convert hrun using 2
    rfl

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
