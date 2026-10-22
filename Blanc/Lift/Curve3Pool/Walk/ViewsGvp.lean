import Blanc.Lift.Curve3Pool.Walk.ViewsKit

/-!
# `get_virtual_price()` on the derivation, part 1: `_xp` and `_A`

From the body (`0x91c`): the non-payable guard, the frame save of `[0x140, 0x2e0)`, the call of
`_xp` (inline save of `[0x140, 0x220)`, results to `0x240…0x280`, copied to `0x300…0x340`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: gvpXp
/-- **`get_virtual_price` up to `_A`'s frame save**: no value; the thirteen saved words on
the stack; `xpChk s.balances` at `0x300…0x340`. -/
theorem xa_gvp_xp (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0x91c (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ ∃ x0 x1 x2 b1 ws M G1, SloadsOnly sevm b b1 ∧ ws.length = 13 ∧
      XAt sevm post 0x9be (St b1 ws M G1) L ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      VW M [(0x340, x2), (0x320, x1), (0x300, x0)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x91d (.reg .callvalue) ri_callvalue  -- 091c CALLVALUE
  xs 0x91e (.reg .iszero) ri_iszero  -- 091d ISZERO
  xs 0x921 (.push [0x09, 0x26] (by decide)) ri_push  -- 091e PUSH2 0x0926
  xji 0x922 0x926 hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x927  -- 0926 JUMPDEST
  xs 0x92a (.push [0x01, 0x40] (by decide)) ri_push  -- 0927 PUSH2 0x0140
  xs 0x92d (.push [0x02, 0xe0] (by decide)) ri_push  -- 092a PUSH2 0x02e0
  xsw 0x92e 0x2e0  -- 092d MSTORE
  -- the save loop over [0x140, 0x2e0)
  obtain ⟨ws, M, _, hws, -, h, hV1⟩ := xa_saveV (H := 0x92e) (t := ⟨0x02, 0xe0, 0x02, 0xe0, 0x09, 0x50, 0x09, 0x2e⟩)
    (lo := 0x140) (n := 13) vsave (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x954 (.push [0x03, 0x00] (by decide)) ri_push  -- 0951 PUSH2 0x0300
  xs 0x957 (.push [0x01, 0x40] (by decide)) ri_push  -- 0954 PUSH2 0x0140
  xlu 0x958  -- 0957 MLOAD
  xs 0x95b (.push [0x01, 0x60] (by decide)) ri_push  -- 0958 PUSH2 0x0160
  xlu 0x95c  -- 095b MLOAD
  xs 0x95f (.push [0x01, 0x80] (by decide)) ri_push  -- 095c PUSH2 0x0180
  xlu 0x960  -- 095f MLOAD
  xs 0x963 (.push [0x01, 0xa0] (by decide)) ri_push  -- 0960 PUSH2 0x01a0
  xlu 0x964  -- 0963 MLOAD
  xs 0x967 (.push [0x01, 0xc0] (by decide)) ri_push  -- 0964 PUSH2 0x01c0
  xlu 0x968  -- 0967 MLOAD
  xs 0x96b (.push [0x01, 0xe0] (by decide)) ri_push  -- 0968 PUSH2 0x01e0
  xlu 0x96c  -- 096b MLOAD
  xs 0x96f (.push [0x02, 0x00] (by decide)) ri_push  -- 096c PUSH2 0x0200
  xlu 0x970  -- 096f MLOAD
  xs 0x972 (.push [0x06] (by decide)) ri_push  -- 0970 PUSH1 0x06
  cvpc 0x973  -- 0972 PC
  xs 0x974 (.reg .add) ri_add  -- 0973 ADD
  xs 0x977 (.push [0x02, 0x81] (by decide)) ri_push  -- 0974 PUSH2 0x0281
  xjmp 0x281
  obtain ⟨x0, x1, x2, b1, M, G1, hb1, h, hx, hV1⟩ := xa_vXp hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x979  -- 0978 JUMPDEST
  xs 0x97c (.push [0x02, 0x40] (by decide)) ri_push  -- 0979 PUSH2 0x0240
  xsw 0x97d 0x240  -- 097c MSTORE
  xs 0x980 (.push [0x02, 0x60] (by decide)) ri_push  -- 097d PUSH2 0x0260
  xsw 0x981 0x260  -- 0980 MSTORE
  xs 0x984 (.push [0x02, 0x80] (by decide)) ri_push  -- 0981 PUSH2 0x0280
  xsw 0x985 0x280  -- 0984 MSTORE
  xs 0x988 (.push [0x02, 0x00] (by decide)) ri_push  -- 0985 PUSH2 0x0200
  xsw 0x989 0x200  -- 0988 MSTORE
  xs 0x98c (.push [0x01, 0xe0] (by decide)) ri_push  -- 0989 PUSH2 0x01e0
  xsw 0x98d 0x1e0  -- 098c MSTORE
  xs 0x990 (.push [0x01, 0xc0] (by decide)) ri_push  -- 098d PUSH2 0x01c0
  xsw 0x991 0x1c0  -- 0990 MSTORE
  xs 0x994 (.push [0x01, 0xa0] (by decide)) ri_push  -- 0991 PUSH2 0x01a0
  xsw 0x995 0x1a0  -- 0994 MSTORE
  xs 0x998 (.push [0x01, 0x80] (by decide)) ri_push  -- 0995 PUSH2 0x0180
  xsw 0x999 0x180  -- 0998 MSTORE
  xs 0x99c (.push [0x01, 0x60] (by decide)) ri_push  -- 0999 PUSH2 0x0160
  xsw 0x99d 0x160  -- 099c MSTORE
  xs 0x9a0 (.push [0x01, 0x40] (by decide)) ri_push  -- 099d PUSH2 0x0140
  xsw 0x9a1 0x140  -- 09a0 MSTORE
  xs 0x9a4 (.push [0x02, 0x40] (by decide)) ri_push  -- 09a1 PUSH2 0x0240
  xs 0x9a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 09a4 DUP1
  xl 0x9a6 0x240  -- 09a5 MLOAD
  xs 0x9a7 (.reg (.dup 2)) (ri_dup (by rfl))  -- 09a6 DUP3
  xsw 0x9a8 0x300  -- 09a7 MSTORE
  xs 0x9a9 (.reg (.dup 0)) (ri_dup (by rfl))  -- 09a8 DUP1
  xs 0x9ab (.push [0x20] (by decide)) ri_push  -- 09a9 PUSH1 0x20
  xs 0x9ac (.reg .add) ri_add  -- 09ab ADD
  xl 0x9ad 0x260  -- 09ac MLOAD
  xs 0x9ae (.reg (.dup 2)) (ri_dup (by rfl))  -- 09ad DUP3
  xs 0x9b0 (.push [0x20] (by decide)) ri_push  -- 09ae PUSH1 0x20
  xs 0x9b1 (.reg .add) ri_add  -- 09b0 ADD
  xsw 0x9b2 0x320  -- 09b1 MSTORE
  xs 0x9b3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 09b2 DUP1
  xs 0x9b5 (.push [0x40] (by decide)) ri_push  -- 09b3 PUSH1 0x40
  xs 0x9b6 (.reg .add) ri_add  -- 09b5 ADD
  xl 0x9b7 0x280  -- 09b6 MLOAD
  xs 0x9b8 (.reg (.dup 2)) (ri_dup (by rfl))  -- 09b7 DUP3
  xs 0x9ba (.push [0x40] (by decide)) ri_push  -- 09b8 PUSH1 0x40
  xs 0x9bb (.reg .add) ri_add  -- 09ba ADD
  xsw 0x9bc 0x340  -- 09bb MSTORE
  xs 0x9bd (.reg .pop) ri_pop  -- 09bc POP
  xs 0x9be (.reg .pop) ri_pop  -- 09bd POP
  rw [List.append_nil] at h
  refine ⟨hval, x0, x1, x2, b1, ws, _, _, hb1, hws, h, hx, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

-- SEGMENT: gvpA
/-- **`get_virtual_price` from `_A`'s frame save to the call of `get_D`**: `_A`'s value `amp`
(`aChk`), the frame restored, and `get_D`'s arguments `xp` and `amp` above the return tag. -/
theorem xa_gvp_a (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 : B256}
    {ws : List B256} {M : Mem} (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hV : VW M [(0x340, x2), (0x320, x1), (0x300, x0)])
    (h : XAt sevm post 0x9be (St b ws M G) L) :
    ∃ amp b2 M2 G2 ρ, SloadsOnly sevm b b2 ∧ ρ.toNat = 0xa40 ∧
      XAt sevm post 0x4c9 (St b2 (ρ :: x0 :: x1 :: x2 :: amp :: ws) M2 G2) L ∧
      aChk s sevm.benvStat.time.toNat = some amp.toNat ∧ VW M2 [(0x360, amp)] := by
  xs 0x9c1 (.push [0x01, 0x40] (by decide)) ri_push  -- 09be PUSH2 0x0140
  xs 0x9c4 (.push [0x02, 0xa0] (by decide)) ri_push  -- 09c1 PUSH2 0x02a0
  xsw 0x9c5 0x2a0  -- 09c4 MSTORE
  -- the save loop over [0x140, 0x2a0)
  obtain ⟨ws2, M, _, hws2, -, h, hV1⟩ := xa_saveV (H := 0x9c5) (t := ⟨0x02, 0xa0, 0x02, 0xa0, 0x09, 0xe7, 0x09, 0xc5⟩)
    (lo := 0x140) (n := 11) vsave (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x9ea (.push [0x06] (by decide)) ri_push  -- 09e8 PUSH1 0x06
  cvpc 0x9eb  -- 09ea PC
  xs 0x9ec (.reg .add) ri_add  -- 09eb ADD
  xs 0x9ef (.push [0x00, 0xa9] (by decide)) ri_push  -- 09ec PUSH2 0x00a9
  xjmp 0xa9
  obtain ⟨amp, b2, M, _, hb2, h, hamp, hV1⟩ := xa_vAV hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x9f1  -- 09f0 JUMPDEST
  xs 0x9f4 (.push [0x02, 0xc0] (by decide)) ri_push  -- 09f1 PUSH2 0x02c0
  xsw 0x9f5 0x2c0  -- 09f4 MSTORE
  xs 0x9f8 (.push [0x02, 0x80] (by decide)) ri_push  -- 09f5 PUSH2 0x0280
  xs 0x9fb (.push [0x02, 0xa0] (by decide)) ri_push  -- 09f8 PUSH2 0x02a0
  xsw 0x9fc 0x2a0  -- 09fb MSTORE
  -- the restore loop over [0x140, 0x2a0)
  obtain ⟨M, _, h, -, hV1⟩ := xa_restoreV (H := 0x9fc) (t := ⟨0x02, 0xa0, 0x01, 0x40, 0x0a, 0x1f, 0x09, 0xfc⟩)
    (lo := 0x140) (ts := ws2) vrestore (by rintro rfl; cases hws2) (by decide) (by decide) hV
    (by rfl) (by rw [hws2]; decide) (by rw [hws2]; decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0xa23 (.push [0x02, 0xc0] (by decide)) ri_push  -- 0a20 PUSH2 0x02c0
  xl 0xa24 0x2c0  -- 0a23 MLOAD
  xs 0xa27 (.push [0x03, 0x60] (by decide)) ri_push  -- 0a24 PUSH2 0x0360
  xsw 0xa28 0x360  -- 0a27 MSTORE
  xs 0xa2b (.push [0x03, 0x60] (by decide)) ri_push  -- 0a28 PUSH2 0x0360
  xl 0xa2c 0x360  -- 0a2b MLOAD
  xs 0xa2f (.push [0x03, 0x40] (by decide)) ri_push  -- 0a2c PUSH2 0x0340
  xl 0xa30 0x340  -- 0a2f MLOAD
  xs 0xa33 (.push [0x03, 0x20] (by decide)) ri_push  -- 0a30 PUSH2 0x0320
  xl 0xa34 0x320  -- 0a33 MLOAD
  xs 0xa37 (.push [0x03, 0x00] (by decide)) ri_push  -- 0a34 PUSH2 0x0300
  xl 0xa38 0x300  -- 0a37 MLOAD
  xs 0xa3a (.push [0x06] (by decide)) ri_push  -- 0a38 PUSH1 0x06
  cvpc 0xa3b  -- 0a3a PC
  xs 0xa3c (.reg .add) ri_add  -- 0a3b ADD
  xs 0xa3f (.push [0x04, 0xc9] (by decide)) ri_push  -- 0a3c PUSH2 0x04c9
  xjmp 0x4c9
  refine ⟨amp, b2, _, _, _, hb2, by decide, h, hamp, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, List.nil_subset, and_self]

/-- The `totalSupply()` reply word. -/
abbrev vSupply (c : Exec.Frame) : B256 := Bytes.toB256 (c.post.output.take 32)

-- SEGMENT: gvpD
/-- **`get_virtual_price` from the call of `get_D` to its `RETURN`**: `D = getDChk xp amp`, the
frame restored, `totalSupply()` read from the token (the frame's only child, static, a word
back), `D · 10^18` unchecked-free and the supply nonzero; storage and logs kept, the output
`D · 10^18 / supply`. -/
theorem xa_gvp_d (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {x0 x1 x2 amp ρ : B256} {ws : List B256} {M : Mem} (hρ : ρ.toNat = 0xa40)
    (hws : ws.length = 13) (hV : VW M [(0x360, amp)])
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x4c9 (St b (ρ :: x0 :: x1 :: x2 :: amp :: ws) M G) L) :
    ∃ c D, L = [c] ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get tokenSlot).toAdr ∧
      c.sevm.data = totalSupplyData ∧ c.sevm.isStatic = true ∧ 32 ≤ c.post.output.length ∧
      c.post.logs = [] ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp.toNat 1 = some D.toNat ∧
      (D * Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] / D =
        Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] ∨ D = 0) ∧
      vSupply c ≠ 0 ∧ (∀ a, post.getStor a = b.getStor a) ∧ post.logs = b.logs ∧
      post.output = (D * Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] /
        vSupply c).toBytes := by
  have hcov : 0x340 ≤ M.size := by
    have := (hV.words 0x360 amp List.mem_cons_self).1
    omega
  obtain ⟨D, M, _, h, hD, -, hV1⟩ := xa_vGetD hc hcode hfork hV hcov h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  rw [hρ] at h
  xjd 0xa41  -- 0a40 JUMPDEST
  xs 0xa44 (.push [0x03, 0xc0] (by decide)) ri_push  -- 0a41 PUSH2 0x03c0
  xsw 0xa45 0x3c0  -- 0a44 MSTORE
  xs 0xa48 (.push [0x02, 0xc0] (by decide)) ri_push  -- 0a45 PUSH2 0x02c0
  xs 0xa4b (.push [0x02, 0xe0] (by decide)) ri_push  -- 0a48 PUSH2 0x02e0
  xsw 0xa4c 0x2e0  -- 0a4b MSTORE
  -- the restore loop over [0x140, 0x2e0)
  rw [← List.append_nil ws] at h
  obtain ⟨M, _, h, -, hV1⟩ := xa_restoreV (H := 0xa4c) (t := ⟨0x02, 0xe0, 0x01, 0x40, 0x0a, 0x6f, 0x0a, 0x4c⟩)
    (lo := 0x140) (ts := ws) vrestore (by rintro rfl; cases hws) (by decide) (by decide) hV
    (by rfl) (by rw [hws]; decide) (by rw [hws]; decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0xa73 (.push [0x03, 0xc0] (by decide)) ri_push  -- 0a70 PUSH2 0x03c0
  xl 0xa74 0x3c0  -- 0a73 MLOAD
  xs 0xa77 (.push [0x01, 0x40] (by decide)) ri_push  -- 0a74 PUSH2 0x0140
  xsw 0xa78 0x140  -- 0a77 MSTORE
  xs 0xa7a (.push [0x20] (by decide)) ri_push  -- 0a78 PUSH1 0x20
  xs 0xa7d (.push [0x04, 0x60] (by decide)) ri_push  -- 0a7a PUSH2 0x0460
  xs 0xa7f (.push [0x04] (by decide)) ri_push  -- 0a7d PUSH1 0x04
  xs 0xa84 (.push [0x18, 0x16, 0x0d, 0xdd] (by decide)) ri_push  -- 0a7f PUSH4 0x18160ddd
  xs 0xa87 (.push [0x04, 0x00] (by decide)) ri_push  -- 0a84 PUSH2 0x0400
  have hW0 := hV.wf
  xsw 0xa88 0x400  -- 0a87 MSTORE
  xs 0xa8b (.push [0x04, 0x1c] (by decide)) ri_push  -- 0a88 PUSH2 0x041c
  xs 0xa8d (.push [0x05] (by decide)) ri_push  -- 0a8b PUSH1 0x05
  xw 0xa8e (.reg .sload) ri_sload  -- 0a8d SLOAD
  xs 0xa8f (.reg .gas) ri_gas_remaining  -- 0a8e GAS
  obtain ⟨d, flag, out, M', L1, h, hVo, hrd, hob, hstor, hlogs, hk⟩ :=
    xa_staticcallV (pc' := 0xa90) (o := 0x460) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl hV h
  clear hV
  xs 0xa93 (.push [0x0a, 0x98] (by decide)) ri_push  -- 0a90 PUSH2 0x0a98
  xji 0xa94 0xa98 hw
  · xdead  -- 0a93 JUMPI
  xjd 0xa99  -- 0a98 JUMPDEST
  xs 0xa9b (.push [0x1f] (by decide)) ri_push  -- 0a99 PUSH1 0x1f
  xs 0xa9c (.reg .returndatasize) ri_returndatasize  -- 0a9b RETURNDATASIZE
  xs 0xa9d (.reg .gt) ri_gt  -- 0a9c GT
  xs 0xaa0 (.push [0x0a, 0xa5] (by decide)) ri_push  -- 0a9d PUSH2 0x0aa5
  have hwf := hw
  clear hw
  rcases hk hwf with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre (by rw [getStorVal_eq, tokenSlot_lit]; exact htok)
  clear hk
  xji 0xaa1 0xaa5 hw
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := gtCheck_ne_zero hw
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw
  have hV := hVo hlen
  clear hVo
  vnorm
  xjd 0xaa6  -- 0aa5 JUMPDEST
  xs 0xaa8 (.push [0x00] (by decide)) ri_push  -- 0aa6 PUSH1 0x00
  xs 0xaa9 (.reg .pop) ri_pop  -- 0aa8 POP
  xs 0xaac (.push [0x04, 0x60] (by decide)) ri_push  -- 0aa9 PUSH2 0x0460
  xl 0xaad 0x460  -- 0aac MLOAD
  xs 0xab0 (.push [0x03, 0xe0] (by decide)) ri_push  -- 0aad PUSH2 0x03e0
  xsw 0xab1 0x3e0  -- 0ab0 MSTORE
  xs 0xab4 (.push [0x01, 0x40] (by decide)) ri_push  -- 0ab1 PUSH2 0x0140
  xl 0xab5 0x140  -- 0ab4 MLOAD
  xs 0xabe (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push  -- 0ab5 PUSH8 0x0de0b6b3a7640000
  xs 0xabf (.reg (.dup 0)) (ri_dup (by rfl))  -- 0abe DUP1
  xs 0xac0 (.reg (.dup 2)) (ri_dup (by rfl))  -- 0abf DUP3
  xs 0xac1 (.reg .mul) ri_mul  -- 0ac0 MUL
  xs 0xac2 (.reg (.dup 2)) (ri_dup (by rfl))  -- 0ac1 DUP3
  xs 0xac3 (.reg .iszero) ri_iszero  -- 0ac2 ISZERO
  xs 0xac4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 0ac3 DUP3
  xs 0xac5 (.reg (.dup 4)) (ri_dup (by rfl))  -- 0ac4 DUP5
  xs 0xac6 (.reg (.dup 3)) (ri_dup (by rfl))  -- 0ac5 DUP4
  xs 0xac7 (.reg .div) ri_div  -- 0ac6 DIV
  xs 0xac8 (.reg .eq) ri_eq  -- 0ac7 EQ
  xs 0xac9 (.reg .or) ri_or  -- 0ac8 OR
  xs 0xacc (.push [0x0a, 0xd1] (by decide)) ri_push  -- 0ac9 PUSH2 0x0ad1
  xji 0xacd 0xad1 hw
  · xdead
  have hmul := or_ne_zero hw
  clear hw
  xjd 0xad2  -- 0ad1 JUMPDEST
  xs 0xad3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 0ad2 DUP1
  xs 0xad4 (.reg (.swap 0)) (ri_swap (by rfl))  -- 0ad3 SWAP1
  xs 0xad5 (.reg .pop) ri_pop  -- 0ad4 POP
  xs 0xad6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 0ad5 SWAP1
  xs 0xad7 (.reg .pop) ri_pop  -- 0ad6 POP
  xs 0xad8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 0ad7 SWAP1
  xs 0xad9 (.reg .pop) ri_pop  -- 0ad8 POP
  xs 0xadc (.push [0x03, 0xe0] (by decide)) ri_push  -- 0ad9 PUSH2 0x03e0
  xl 0xadd 0x3e0  -- 0adc MLOAD
  xs 0xade (.reg (.dup 0)) (ri_dup (by rfl))  -- 0add DUP1
  xs 0xadf (.reg (.dup 0)) (ri_dup (by rfl))  -- 0ade DUP1
  xs 0xae2 (.push [0x0a, 0xe7] (by decide)) ri_push  -- 0adf PUSH2 0x0ae7
  xji 0xae3 0xae7 hw
  · xdead
  have hT := hw
  clear hw
  xjd 0xae8  -- 0ae7 JUMPDEST
  xs 0xae9 (.reg (.dup 2)) (ri_dup (by rfl))  -- 0ae8 DUP3
  xs 0xaea (.reg .div) ri_div  -- 0ae9 DIV
  xs 0xaeb (.reg (.swap 0)) (ri_swap (by rfl))  -- 0aea SWAP1
  xs 0xaec (.reg .pop) ri_pop  -- 0aeb POP
  xs 0xaed (.reg (.swap 0)) (ri_swap (by rfl))  -- 0aec SWAP1
  xs 0xaee (.reg .pop) ri_pop  -- 0aed POP
  xs 0xaf0 (.push [0x00] (by decide)) ri_push  -- 0aee PUSH1 0x00
  xsw 0xaf1 0x0  -- 0af0 MSTORE
  xs 0xaf3 (.push [0x20] (by decide)) ri_push  -- 0af1 PUSH1 0x20
  xs 0xaf5 (.push [0x00] (by decide)) ri_push  -- 0af3 PUSH1 0x00
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor', hlogs'⟩ := ri_return hrun
  subst hcout
  refine ⟨c, D, hL, ?_, ?_, hstat, hlen, hclogs, hD, ?_, hT, ?_, ?_, ?_⟩
  · rw [htgt, getStorVal_eq, tokenSlot_lit]
  · rw [hdata, show (Bytes.toB256 [4, 28]).toNat = 1052 from rfl,
      show (Bytes.toB256 [4]).toNat = 4 from rfl,
      Mem.read_write_word_inside hW0 1024 _ (by decide) (by decide)]
    decide
  · rcases hmul with h1 | h1
    · exact .inl (eqCheck_ne_zero_eq h1)
    · exact .inr (eqCheck_ne_zero_eq h1)
  · intro a
    rw [hstor', hstor, afterSload_getStor]
  · rw [hlogs', hlogs, afterSload_logs]
  · generalize (M'.write 992 _).write 0 _ = Mf at hV hout
    have hl0 : (Mf.read 0 32).1.length = 32 := by
      simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
    have hv : Bytes.toB256 (Mf.read 0 32).1 = _ := hV.words.memWord (o := 0) List.mem_cons_self
    rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl, show (Bytes.toB256 [32]).toNat = 32 from rfl,
      ← Bytes.toBytes_toB256_of_length hl0, hv]


end

end Blanc.Lift.Curve3Pool
