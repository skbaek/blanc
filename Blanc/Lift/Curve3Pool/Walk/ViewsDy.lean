import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.ViewsDyKit
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `get_dy(i, j, dx)` on the derivation

From the body (`0x1d22`): the non-payable guard, the `int128` clamps of `i` and `j`, `RATES` at
`0x140…0x180`, `_xp` (results copied to `0x1a0…0x1e0`), `x = xp[i] + dx · RATES[i] / 10^18`
at `0x280`; the frame save of `[0x140, 0x2c0)`, `get_y(i, j, x, xp)`, the frame restore, and
`dy = (xp[j] - y - 1) · 10^18 / RATES[j]`, `fee = self.fee · dy / 10^10`, `dy - fee`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The decoded arguments `i`, `j`, `dx`. -/
abbrev dyI (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev dyJ (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x24])
abbrev dyDx (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x44])

/-- `PRECISION` and `10^30`, as pushed. -/
abbrev rP : B256 := Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00]
abbrev rQ : B256 :=
  Bytes.toB256 [0x0c, 0x9f, 0x2c, 0x9c, 0xd0, 0x46, 0x74, 0xed, 0xea, 0x40, 0x00, 0x00, 0x00]

/-- `x = xp[i] + dx · RATES[i] / PRECISION`, as words. -/
abbrev dyX (sevm : Sevm) (x0 x1 x2 : B256) : B256 :=
  pickWord3 (dyI sevm).toNat x0 x1 x2 + dyDx sevm * pickWord3 (dyI sevm).toNat rP rQ rQ / rP

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: dyX
/-- **`get_dy` up to the frame save before `get_y`.** -/
theorem xa_dy_x (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0x1d22 (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ ∃ (x0 x1 x2 : B256) (b1 : Devm) (M : Mem) (G1 : Nat), SloadsOnlyH sevm b b1 ∧
      (dyI sevm).toNat < 3 ∧ xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      B256.Nofm (dyDx sevm) (pickWord3 (dyI sevm).toNat rP rQ rQ) ∧
      (pickWord3 (dyI sevm).toNat x0 x1 x2).toNat +
        (dyDx sevm * pickWord3 (dyI sevm).toNat rP rQ rQ / rP).toNat < 2 ^ 256 ∧
      XAt sevm post 0x1e9a (St b1 [] M G1) L ∧
      VW M [(0x2c0, Bytes.toB256 [1, 64]), (0x280, dyX sevm x0 x1 x2), (0x140, rP), (0x160, rQ),
        (0x180, rQ), (0x1a0, x0), (0x1c0, x1), (0x1e0, x2)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xa 3
  xji 0x1d28 0x1d2c hw
  · xdead  -- 1d27 JUMPI
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xlu 0x1d30  -- 1d2f MLOAD
  xa 4
  xlu 0x1d37  -- 1d36 MLOAD
  xa 4
  xji 0x1d3e 0x1d42 hw
  · xdead  -- 1d3d JUMPI
  clear hw
  xa 7
  xji 0x1d4c 0x1d50 hw
  · xdead  -- 1d4b JUMPI
  clear hw
  xa 3
  xlu 0x1d55  -- 1d54 MLOAD
  xa 4
  xlu 0x1d5c  -- 1d5b MLOAD
  xa 4
  xji 0x1d63 0x1d67 hw
  · xdead  -- 1d62 JUMPI
  clear hw
  xa 7
  xji 0x1d71 0x1d75 hw
  · xdead  -- 1d70 JUMPI
  clear hw
  xa 5
  xsw 0x1d85 0x140  -- 1d84 MSTORE
  xa 4
  xsw 0x1d98 0x160  -- 1d97 MSTORE
  xa 4
  xsw 0x1dab 0x180  -- 1daa MSTORE
  xa 3
  xl 0x1db3 0x140  -- 1db2 MLOAD
  xs 0x1db6 (.push [0x01, 0x60] (by decide)) ri_push  -- 1db3 PUSH2 0x0160
  xl 0x1db7 0x160  -- 1db6 MLOAD
  xs 0x1dba (.push [0x01, 0x80] (by decide)) ri_push  -- 1db7 PUSH2 0x0180
  xl 0x1dbb 0x180  -- 1dba MLOAD
  xs 0x1dbe (.push [0x01, 0xa0] (by decide)) ri_push  -- 1dbb PUSH2 0x01a0
  xlu 0x1dbf  -- 1dbe MLOAD
  xs 0x1dc2 (.push [0x01, 0xc0] (by decide)) ri_push  -- 1dbf PUSH2 0x01c0
  xlu 0x1dc3  -- 1dc2 MLOAD
  xs 0x1dc6 (.push [0x01, 0xe0] (by decide)) ri_push  -- 1dc3 PUSH2 0x01e0
  xlu 0x1dc7  -- 1dc6 MLOAD
  xs 0x1dc9 (.push [0x06] (by decide)) ri_push  -- 1dc7 PUSH1 0x06
  cvpc 0x1dca  -- 1dc9 PC
  xa 2
  xjmp 0x281  -- 1dce JUMP
  obtain ⟨x0, x1, x2, b1, M, G1, hb1, h, hx, hV1⟩ := xa_vXp hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x1dd4 0x220  -- 1dd3 MSTORE
  xs 0x1dd7 (.push [0x02, 0x40] (by decide)) ri_push  -- 1dd4 PUSH2 0x0240
  xsw 0x1dd8 0x240  -- 1dd7 MSTORE
  xs 0x1ddb (.push [0x02, 0x60] (by decide)) ri_push  -- 1dd8 PUSH2 0x0260
  xsw 0x1ddc 0x260  -- 1ddb MSTORE
  xs 0x1ddf (.push [0x01, 0xe0] (by decide)) ri_push  -- 1ddc PUSH2 0x01e0
  xsw 0x1de0 0x1e0  -- 1ddf MSTORE
  xs 0x1de3 (.push [0x01, 0xc0] (by decide)) ri_push  -- 1de0 PUSH2 0x01c0
  xsw 0x1de4 0x1c0  -- 1de3 MSTORE
  xs 0x1de7 (.push [0x01, 0xa0] (by decide)) ri_push  -- 1de4 PUSH2 0x01a0
  xsw 0x1de8 0x1a0  -- 1de7 MSTORE
  xs 0x1deb (.push [0x01, 0x80] (by decide)) ri_push  -- 1de8 PUSH2 0x0180
  xsw 0x1dec 0x180  -- 1deb MSTORE
  xs 0x1def (.push [0x01, 0x60] (by decide)) ri_push  -- 1dec PUSH2 0x0160
  xsw 0x1df0 0x160  -- 1def MSTORE
  xs 0x1df3 (.push [0x01, 0x40] (by decide)) ri_push  -- 1df0 PUSH2 0x0140
  xsw 0x1df4 0x140  -- 1df3 MSTORE
  xa 2
  xl 0x1df9 0x220  -- 1df8 MLOAD
  xs 0x1dfa (.reg (.dup 2)) (ri_dup (by rfl))  -- 1df9 DUP3
  xsw 0x1dfb 0x1a0  -- 1dfa MSTORE
  xa 3
  xl 0x1e00 0x240  -- 1dff MLOAD
  xa 3
  xsw 0x1e05 0x1c0  -- 1e04 MSTORE
  xa 3
  xl 0x1e0a 0x260  -- 1e09 MLOAD
  xa 3
  xsw 0x1e0f 0x1e0  -- 1e0e MSTORE
  xa 9
  xji 0x1e1f 0x1e23 hw
  · xdead  -- 1e1e JUMPI
  have hi := ltCheck_ne_zero hw
  rw [show (Bytes.toB256 [3]).toNat = 3 from rfl] at hi
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1e29) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x1a0) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xa 9
  xji 0x1e3a 0x1e3e hw
  · xdead  -- 1e39 JUMPI
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1e44) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xa 12
  xji 0x1e53 0x1e57 hw
  · xdead  -- 1e52 JUMPI
  have hmx := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x1e6e 0x1e72 hw
  · xdead  -- 1e6d JUMPI
  clear hw
  xa 14
  xji 0x1e83 0x1e87 hw
  · xdead  -- 1e82 JUMPI
  have hax := (B256.nof_iff_not_add_lt _ _).mpr
    (B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xa 9
  xsw 0x1e93 0x280  -- 1e92 MSTORE
  xa 2
  xsw 0x1e9a 0x2c0  -- 1e99 MSTORE

  refine ⟨hval, x0, x1, x2, b1, _, _, hb1, hi, hx, hmx, hax, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

-- SEGMENT: dyY
/-- **`get_dy` from the frame save to past the frame restore around `get_y`.** -/
theorem xa_dy_y (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork) {x0 x1 x2 X : B256}
    {M : Mem} (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hV : VW M [(0x2c0, Bytes.toB256 [1, 64]), (0x280, X), (0x140, rP), (0x160, rQ), (0x180, rQ),
      (0x1a0, x0), (0x1c0, x1), (0x1e0, x2)])
    (h : XAt sevm post 0x1e9a (St b [] M G) L) :
    ∃ (y : B256) (b2 : Devm) (M2 : Mem) (G2 : Nat), SloadsOnlyH sevm b b2 ∧
      XAt sevm post 0x1f43 (St b2 [] M2 G2) L ∧
      ∃ amp, aChk s sevm.benvStat.time.toNat = some amp ∧
      ∃ (hi : (dyI sevm).toNat < 3) (hj : (dyJ sevm).toNat < 3),
        getYChk amp ⟨(dyI sevm).toNat, hi⟩ ⟨(dyJ sevm).toNat, hj⟩ X.toNat
          (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
      VW M2 [(0x3e0, y), (0x140, rP), (0x160, rQ), (0x180, rQ), (0x1a0, x0), (0x1c0, x1),
        (0x1e0, x2)] := by
  have hF : Words M [(0x140, rP), (0x160, rQ), (0x180, rQ), (0x1a0, x0), (0x1c0, x1),
      (0x1e0, x2)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x2c0)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x1e9a)
    (t := ⟨0x02, 0xc0, 0x02, 0xc0, 0x1e, 0xbc, 0x1e, 0x9a⟩) (lo := 0x140) (n := 12) vsave (by decide)
    hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 3
  xsw 0x1ec4 0x2e0  -- 1ec3 MSTORE
  xa 3
  xsw 0x1ecb 0x300  -- 1eca MSTORE
  xs 0x1ece (.push [0x02, 0x80] (by decide)) ri_push  -- 1ecb PUSH2 0x0280
  xl 0x1ecf 0x280  -- 1ece MLOAD
  xs 0x1ed2 (.push [0x03, 0x20] (by decide)) ri_push  -- 1ecf PUSH2 0x0320
  xsw 0x1ed3 0x320  -- 1ed2 MSTORE
  xa 3
  xl 0x1edb 0x1a0  -- 1eda MLOAD
  xs 0x1edc (.reg (.dup 2)) (ri_dup (by rfl))  -- 1edb DUP3
  xsw 0x1edd 0x340  -- 1edc MSTORE
  xa 3
  xl 0x1ee2 0x1c0  -- 1ee1 MLOAD
  xa 3
  xsw 0x1ee7 0x360  -- 1ee6 MSTORE
  xa 3
  xl 0x1eec 0x1e0  -- 1eeb MLOAD
  xa 3
  xsw 0x1ef1 0x380  -- 1ef0 MSTORE
  xa 3
  xl 0x1ef7 0x380  -- 1ef6 MLOAD
  xs 0x1efa (.push [0x03, 0x60] (by decide)) ri_push  -- 1ef7 PUSH2 0x0360
  xl 0x1efb 0x360  -- 1efa MLOAD
  xs 0x1efe (.push [0x03, 0x40] (by decide)) ri_push  -- 1efb PUSH2 0x0340
  xl 0x1eff 0x340  -- 1efe MLOAD
  xs 0x1f02 (.push [0x03, 0x20] (by decide)) ri_push  -- 1eff PUSH2 0x0320
  xl 0x1f03 0x320  -- 1f02 MLOAD
  xs 0x1f06 (.push [0x03, 0x00] (by decide)) ri_push  -- 1f03 PUSH2 0x0300
  xl 0x1f07 0x300  -- 1f06 MLOAD
  xs 0x1f0a (.push [0x02, 0xe0] (by decide)) ri_push  -- 1f07 PUSH2 0x02e0
  xl 0x1f0b 0x2e0  -- 1f0a MLOAD
  xs 0x1f0d (.push [0x06] (by decide)) ri_push  -- 1f0b PUSH1 0x06
  cvpc 0x1f0e  -- 1f0d PC
  xa 2
  xjmp 0x18a4  -- 1f12 JUMP
  obtain ⟨y, M3, _, h, amp, hamp, hi, hj, hy, hV1⟩ := xa_vGetY hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x1f18 0x3e0  -- 1f17 MSTORE
  xa 2
  xsw 0x1f1f 0x2c0  -- 1f1e MSTORE
  -- the restore loop over [0x140, 0x2c0)
  rw [← List.append_nil (frameWords _ _ _).reverse] at h
  obtain ⟨M4, _, h, hV1⟩ := xa_restoreFrameV (H := 0x1f1f)
    (t := ⟨0x02, 0xc0, 0x01, 0x40, 0x1f, 0x42, 0x1f, 0x1f⟩) (lo := 0x140) (n := 12) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
      · exact ⟨4, by decide, rfl⟩
      · exact ⟨5, by decide, rfl⟩) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  refine ⟨y, _, M4, _, aBaseH_sloadsOnly sevm b, h, amp, hamp, hi, hj, hy, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_append, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
