import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceD0
import Blanc.Lift.FrameWalkAligned
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `remove_liquidity_imbalance` on the word carrier, part 3: `D1`

`xa_rli_d1` (`0x32ba` → the fee loop's head `0x336e`): the frame save of `[0x140, 0x4a0)`,
`D1 = get_D_mem(new_balances, amp)`, the restore, `D1` at `0x480`, `fees = empty(uint256[3])`
(a `CALLDATACOPY` from past the calldata, `ri_calldatacopyV`), and the fee loop's counter at
`0x600`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
  {LW : List (Nat × B256)}

/-- `CALLDATACOPY` at a literal offset over the carrier: the carried words off the copied range
survive. -/
theorem ri_calldatacopyV {di si sz : B256} {o z : Nat} (hV : VW M LW) (ho : di.toNat = o)
    (hz : sz.toNat = z)
    (h : Ninst.Run sevm (St b (di :: si :: sz :: S) M G) (.reg .calldatacopy) d) :
    ∃ M' G', d = St b S M' G' ∧ VW M' (wordsOffR o (o + z) LW) := by
  obtain ⟨G', rfl⟩ := ri_calldatacopy h
  refine ⟨_, G', rfl, ⟨(hV.words.sub (List.filter_subset_self _)).agree (Mem.write_agree M _ _)
    fun o' v hm => ?_, hV.wf.write _ _, Blanc.Lift.Mem.size_write_mod32 hV.al⟩⟩
  have h' := (List.mem_filter.mp hm).2
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rw [List.length_sliceD, ho, hz]
  omega

end

set_option hygiene false in
/-- `CALLDATACOPY` at a literal offset and size (carrier `hV`). -/
local macro "xcdc " pc:term:max o:term:max z:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := .reg .calldatacopy) (pc' := $pc) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  have e := ri_calldatacopyV (o := $o) (z := $z) hV (by rfl) (by rfl) s
  clear s hV
  obtain ⟨_, _, rfl, hV⟩ := e
  vnorm))

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

-- SEGMENT: rliD1
/-- **`D1`, `fees` and the fee loop's counter** (`0x32ba` → `0x336e`). -/
theorem xa_rli_d1 (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    {M : Mem} {D0 T F AF A o0 o1 o2 n0 n1 n2 : B256}
    (hV : VW M [(0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1),
      (0x2c0, o2), (0x2e0, n0), (0x300, n1), (0x320, n2)])
    (h : XAt sevm post 0x32ba (St b [] M G) L) :
    ∃ (D1 : B256) (M' : Mem) (G' : Nat),
      getDMem ⟨n0.toNat, n1.toNat, n2.toNat⟩ A.toNat = some D1.toNat ∧
      XAt sevm post 0x336e (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M' G') L ∧
      VW M' [(0x600, Bytes.toB256 [0]), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F),
        (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, n0), (0x300, n1),
        (0x320, n2)] := by
  xa 2
  xsw 0x32c1 0x4a0  -- 32c0 MSTORE
  have hF : Words _ [(0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1),
      (0x2c0, o2), (0x2e0, n0), (0x300, n1), (0x320, n2)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x4a0)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x32c1)
    (t := ⟨0x04, 0xa0, 0x04, 0xa0, 0x32, 0xe3, 0x32, 0xc1⟩) (lo := 0x140) (n := 27) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 3
  xl 0x32ec 0x2e0  -- 32eb MLOAD
  xs 0x32ed (.reg (.dup 2)) (ri_dup (by rfl))  -- 32ec DUP3
  xsw 0x32ee 0x4c0  -- 32ed MSTORE
  xa 3
  xl 0x32f3 0x300  -- 32f2 MLOAD
  xa 3
  xsw 0x32f8 0x4e0  -- 32f7 MSTORE
  xa 3
  xl 0x32fd 0x320  -- 32fc MLOAD
  xa 3
  xsw 0x3302 0x500  -- 3301 MSTORE
  xa 3
  xl 0x3308 0x220  -- 3307 MLOAD
  xs 0x330b (.push [0x05, 0x20] (by decide)) ri_push  -- 3308 PUSH2 0x0520
  xsw 0x330c 0x520  -- 330b MSTORE
  xs 0x330f (.push [0x05, 0x20] (by decide)) ri_push  -- 330c PUSH2 0x0520
  xl 0x3310 0x520  -- 330f MLOAD
  xs 0x3313 (.push [0x05, 0x00] (by decide)) ri_push  -- 3310 PUSH2 0x0500
  xl 0x3314 0x500  -- 3313 MLOAD
  xs 0x3317 (.push [0x04, 0xe0] (by decide)) ri_push  -- 3314 PUSH2 0x04e0
  xl 0x3318 0x4e0  -- 3317 MLOAD
  xs 0x331b (.push [0x04, 0xc0] (by decide)) ri_push  -- 3318 PUSH2 0x04c0
  xl 0x331c 0x4c0  -- 331b MLOAD
  xs 0x331e (.push [0x06] (by decide)) ri_push  -- 331c PUSH1 0x06
  cvpc 0x331f  -- 331e PC
  xa 2
  xjmp 0x7b7  -- 3323 JUMP
  obtain ⟨D1, M3, _, h, hD1, hV1⟩ := xa_vGetDMem hc hcode hfork hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x3329 0x580  -- 3328 MSTORE
  xa 2
  xsw 0x3330 0x4a0  -- 332f MSTORE
  -- the restore loop over [0x140, 0x4a0)
  rw [← List.append_nil (frameWords _ _ _).reverse] at h
  obtain ⟨M4, _, h, hV1⟩ := xa_restoreFrameV (H := 0x3330)
    (t := ⟨0x04, 0xa0, 0x01, 0x40, 0x33, 0x53, 0x33, 0x30⟩) (lo := 0x140) (n := 27) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      refine ⟨(o - 0x140) / 32, ?_, ?_⟩ <;>
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm <;>
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) h
  simp only [List.cons_append, List.nil_append] at hV1
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x3357 (.push [0x05, 0x80] (by decide)) ri_push  -- 3354 PUSH2 0x0580
  xl 0x3358 0x580  -- 3357 MLOAD
  xs 0x335b (.push [0x04, 0x80] (by decide)) ri_push  -- 3358 PUSH2 0x0480
  xsw 0x335c 0x480  -- 335b MSTORE
  xa 3
  xcdc 0x3363 0x5a0 0x60  -- 3362 CALLDATACOPY
  xa 5
  xsw 0x336d 0x600  -- 336c MSTORE
  xs 0x336e (.reg .add) ri_add  -- 336d ADD
  rw [show Bytes.toB256 [3] + Bytes.toB256 [0] = Bytes.toB256 [3] from by decide] at h
  refine ⟨D1, _, _, hD1, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
