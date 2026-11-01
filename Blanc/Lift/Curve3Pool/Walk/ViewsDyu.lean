import Blanc.Lift.Curve3Pool.Walk.ViewsDyPost
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `get_dy_underlying(i, j, dx)` on the derivation

From the body (`0x2054`): the non-payable guard, the `int128` clamps of `i` and `j`, `_xp`
(results at `0x1c0…0x200`, copied to `0x140…0x180`), `PRECISION_MUL` at `0x220…0x260`,
`x = xp[i] + dx · PRECISION_MUL[i]` at `0x280`; the frame save of `[0x140, 0x2c0)`,
`get_y(i, j, x, xp)`, the frame restore, and `dy = (xp[j] - y - 1) / PRECISION_MUL[j]`,
`fee = self.fee · dy / 10^10`, `dy - fee`. The arguments are `get_dy`'s (`dyI`, `dyJ`, `dyDx`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- `PRECISION_MUL`'s words as pushed: `1` and `10^12`. -/
abbrev dyuP1 : B256 := Bytes.toB256 [0x01]
abbrev dyuPm : B256 := Bytes.toB256 [0xe8, 0xd4, 0xa5, 0x10, 0x00]

/-- `x = xp[i] + dx · PRECISION_MUL[i]`, as words. -/
abbrev dyuX (sevm : Sevm) (x0 x1 x2 : B256) : B256 :=
  pickWord3 (dyI sevm).toNat x0 x1 x2 + dyDx sevm * pickWord3 (dyI sevm).toNat dyuP1 dyuPm dyuPm

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: dyuX
/-- **`get_dy_underlying` up to the frame save before `get_y`.** -/
theorem xa_dyu_x (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0x2054 (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ ∃ (x0 x1 x2 : B256) (b1 : Devm) (M : Mem) (G1 : Nat), SloadsOnly sevm b b1 ∧
      (dyI sevm).toNat < 3 ∧ xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      B256.Nofm (dyDx sevm) (pickWord3 (dyI sevm).toNat dyuP1 dyuPm dyuPm) ∧
      (pickWord3 (dyI sevm).toNat x0 x1 x2).toNat +
        (dyDx sevm * pickWord3 (dyI sevm).toNat dyuP1 dyuPm dyuPm).toNat < 2 ^ 256 ∧
      XAt sevm post 0x2183 (St b1 [] M G1) L ∧
      VW M [(0x2c0, Bytes.toB256 [1, 64]), (0x280, dyuX sevm x0 x1 x2), (0x140, x0), (0x160, x1),
        (0x180, x2), (0x220, dyuP1), (0x240, dyuPm), (0x260, dyuPm)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xa 3
  xji 0x205a 0x205e hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xlu 0x2062  -- 2061 MLOAD
  xa 4
  xlu 0x2069  -- 2068 MLOAD
  xa 4
  xji 0x2070 0x2074 hw
  · xdead
  clear hw
  xa 7
  xji 0x207e 0x2082 hw
  · xdead
  clear hw
  xa 3
  xlu 0x2087  -- 2086 MLOAD
  xa 4
  xlu 0x208e  -- 208d MLOAD
  xa 4
  xji 0x2095 0x2099 hw
  · xdead
  clear hw
  xa 7
  xji 0x20a3 0x20a7 hw
  · xdead
  clear hw
  xa 4
  xlu 0x20b0  -- 20af MLOAD
  xs 0x20b3 (.push [0x01, 0x60] (by decide)) ri_push  -- 20b0 PUSH2 0x0160
  xlu 0x20b4  -- 20b3 MLOAD
  xs 0x20b7 (.push [0x01, 0x80] (by decide)) ri_push  -- 20b4 PUSH2 0x0180
  xlu 0x20b8  -- 20b7 MLOAD
  xs 0x20ba (.push [0x06] (by decide)) ri_push  -- 20b8 PUSH1 0x06
  cvpc 0x20bb  -- 20ba PC
  xa 2
  xjmp 0x281  -- 20bf JUMP
  obtain ⟨x0, x1, x2, b1, M, G1, hb1, h, hx, hV1⟩ := xa_vXp hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x20c5 0x1c0  -- 20c4 MSTORE
  xs 0x20c8 (.push [0x01, 0xe0] (by decide)) ri_push  -- 20c5 PUSH2 0x01e0
  xsw 0x20c9 0x1e0  -- 20c8 MSTORE
  xs 0x20cc (.push [0x02, 0x00] (by decide)) ri_push  -- 20c9 PUSH2 0x0200
  xsw 0x20cd 0x200  -- 20cc MSTORE
  xs 0x20d0 (.push [0x01, 0x80] (by decide)) ri_push  -- 20cd PUSH2 0x0180
  xsw 0x20d1 0x180  -- 20d0 MSTORE
  xs 0x20d4 (.push [0x01, 0x60] (by decide)) ri_push  -- 20d1 PUSH2 0x0160
  xsw 0x20d5 0x160  -- 20d4 MSTORE
  xs 0x20d8 (.push [0x01, 0x40] (by decide)) ri_push  -- 20d5 PUSH2 0x0140
  xsw 0x20d9 0x140  -- 20d8 MSTORE
  xa 2
  xl 0x20de 0x1c0  -- 20dd MLOAD
  xs 0x20df (.reg (.dup 2)) (ri_dup (by rfl))  -- 20de DUP3
  xsw 0x20e0 0x140  -- 20df MSTORE
  xa 3
  xl 0x20e5 0x1e0  -- 20e4 MLOAD
  xa 3
  xsw 0x20ea 0x160  -- 20e9 MSTORE
  xa 3
  xl 0x20ef 0x200  -- 20ee MLOAD
  xa 3
  xsw 0x20f4 0x180  -- 20f3 MSTORE
  xa 5
  xsw 0x20fd 0x220  -- 20fc MSTORE
  xa 4
  xsw 0x2108 0x240  -- 2107 MSTORE
  xa 4
  xsw 0x2113 0x260  -- 2112 MSTORE
  xa 8
  xji 0x2122 0x2126 hw
  · xdead
  have hi := ltCheck_ne_zero hw
  rw [show (Bytes.toB256 [3]).toNat = 3 from rfl] at hi
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x212c) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xa 9
  xji 0x213d 0x2141 hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x2147) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xa 12
  xji 0x2156 0x215a hw
  · xdead
  have hmx := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 15
  xji 0x216c 0x2170 hw
  · xdead
  have hax := (B256.nof_iff_not_add_lt _ _).mpr
    (B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xa 9
  xsw 0x217c 0x280  -- 217b MSTORE
  xa 2
  xsw 0x2183 0x2c0  -- 2182 MSTORE

  refine ⟨hval, x0, x1, x2, b1, _, _, hb1, hi, hx, hmx, hax, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

-- SEGMENT: dyuY
/-- **`get_dy_underlying` from the frame save to past the frame restore around `get_y`.** -/
theorem xa_dyu_y (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 X : B256}
    {M : Mem} (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hV : VW M [(0x2c0, Bytes.toB256 [1, 64]), (0x280, X), (0x140, x0), (0x160, x1), (0x180, x2),
      (0x220, dyuP1), (0x240, dyuPm), (0x260, dyuPm)])
    (h : XAt sevm post 0x2183 (St b [] M G) L) :
    ∃ (y : B256) (b2 : Devm) (M2 : Mem) (G2 : Nat), SloadsOnly sevm b b2 ∧
      XAt sevm post 0x222c (St b2 [] M2 G2) L ∧
      ∃ amp, aChk s sevm.benvStat.time.toNat = some amp ∧
      ∃ (hi : (dyI sevm).toNat < 3) (hj : (dyJ sevm).toNat < 3),
        getYChk amp ⟨(dyI sevm).toNat, hi⟩ ⟨(dyJ sevm).toNat, hj⟩ X.toNat
          (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
      VW M2 [(0x3e0, y), (0x140, x0), (0x160, x1), (0x180, x2), (0x220, dyuP1), (0x240, dyuPm),
        (0x260, dyuPm)] := by
  have hF : Words M [(0x140, x0), (0x160, x1), (0x180, x2), (0x220, dyuP1), (0x240, dyuPm),
      (0x260, dyuPm)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x2c0)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x2183)
    (t := ⟨0x02, 0xc0, 0x02, 0xc0, 0x21, 0xa5, 0x21, 0x83⟩) (lo := 0x140) (n := 12) vsave (by decide)
    hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 3
  xsw 0x21ad 0x2e0  -- 21ac MSTORE
  xa 3
  xsw 0x21b4 0x300  -- 21b3 MSTORE
  xs 0x21b7 (.push [0x02, 0x80] (by decide)) ri_push  -- 21b4 PUSH2 0x0280
  xl 0x21b8 0x280  -- 21b7 MLOAD
  xs 0x21bb (.push [0x03, 0x20] (by decide)) ri_push  -- 21b8 PUSH2 0x0320
  xsw 0x21bc 0x320  -- 21bb MSTORE
  xa 3
  xl 0x21c4 0x140  -- 21c3 MLOAD
  xs 0x21c5 (.reg (.dup 2)) (ri_dup (by rfl))  -- 21c4 DUP3
  xsw 0x21c6 0x340  -- 21c5 MSTORE
  xa 3
  xl 0x21cb 0x160  -- 21ca MLOAD
  xa 3
  xsw 0x21d0 0x360  -- 21cf MSTORE
  xa 3
  xl 0x21d5 0x180  -- 21d4 MLOAD
  xa 3
  xsw 0x21da 0x380  -- 21d9 MSTORE
  xa 3
  xl 0x21e0 0x380  -- 21df MLOAD
  xs 0x21e3 (.push [0x03, 0x60] (by decide)) ri_push  -- 21e0 PUSH2 0x0360
  xl 0x21e4 0x360  -- 21e3 MLOAD
  xs 0x21e7 (.push [0x03, 0x40] (by decide)) ri_push  -- 21e4 PUSH2 0x0340
  xl 0x21e8 0x340  -- 21e7 MLOAD
  xs 0x21eb (.push [0x03, 0x20] (by decide)) ri_push  -- 21e8 PUSH2 0x0320
  xl 0x21ec 0x320  -- 21eb MLOAD
  xs 0x21ef (.push [0x03, 0x00] (by decide)) ri_push  -- 21ec PUSH2 0x0300
  xl 0x21f0 0x300  -- 21ef MLOAD
  xs 0x21f3 (.push [0x02, 0xe0] (by decide)) ri_push  -- 21f0 PUSH2 0x02e0
  xl 0x21f4 0x2e0  -- 21f3 MLOAD
  xs 0x21f6 (.push [0x06] (by decide)) ri_push  -- 21f4 PUSH1 0x06
  cvpc 0x21f7  -- 21f6 PC
  xa 2
  xjmp 0x18a4  -- 21fb JUMP
  obtain ⟨y, M3, _, h, amp, hamp, hi, hj, hy, hV1⟩ := xa_vGetY hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x2201 0x3e0  -- 2200 MSTORE
  xa 2
  xsw 0x2208 0x2c0  -- 2207 MSTORE
  -- the restore loop over [0x140, 0x2c0)
  rw [← List.append_nil (frameWords _ _ _).reverse] at h
  obtain ⟨M4, _, h, hV1⟩ := xa_restoreFrameV (H := 0x2208)
    (t := ⟨0x02, 0xc0, 0x01, 0x40, 0x22, 0x2b, 0x22, 0x08⟩) (lo := 0x140) (n := 12) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨7, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨9, by decide, rfl⟩) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  refine ⟨y, _, M4, _, aBase_sloadsOnly sevm b, h, amp, hamp, hi, hj, hy, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_append, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
