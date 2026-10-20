import Blanc.Lift.Curve3Pool.Walk.ViewsDyKit

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
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0x1d22 (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ ∃ (x0 x1 x2 : B256) (b1 : Devm) (M : Mem) (G1 : Nat), SloadsOnly sevm b b1 ∧
      (dyI sevm).toNat < 3 ∧ xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      B256.Nofm (dyDx sevm) (pickWord3 (dyI sevm).toNat rP rQ rQ) ∧
      (pickWord3 (dyI sevm).toNat x0 x1 x2).toNat +
        (dyDx sevm * pickWord3 (dyI sevm).toNat rP rQ rQ / rP).toNat < 2 ^ 256 ∧
      XAt sevm post 0x1e9a (St b1 [] M G1) L ∧
      VW M [(0x2c0, Bytes.toB256 [1, 64]), (0x280, dyX sevm x0 x1 x2), (0x140, rP), (0x160, rQ),
        (0x180, rQ), (0x1a0, x0), (0x1c0, x1), (0x1e0, x2)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x1d23 (.reg .callvalue) ri_callvalue  -- 1d22 CALLVALUE
  xs 0x1d24 (.reg .iszero) ri_iszero  -- 1d23 ISZERO
  xs 0x1d27 (.push [0x1d, 0x2c] (by decide)) ri_push  -- 1d24 PUSH2 0x1d2c
  xji 0x1d28 0x1d2c hw
  · xdead  -- 1d27 JUMPI
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x1d2d  -- 1d2c JUMPDEST
  xs 0x1d2f (.push [0x60] (by decide)) ri_push  -- 1d2d PUSH1 0x60
  xlu 0x1d30  -- 1d2f MLOAD
  xs 0x1d32 (.push [0x04] (by decide)) ri_push  -- 1d30 PUSH1 0x04
  xs 0x1d33 (.reg .calldataload) ri_calldataload  -- 1d32 CALLDATALOAD
  xs 0x1d34 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1d33 DUP1
  xs 0x1d36 (.push [0x40] (by decide)) ri_push  -- 1d34 PUSH1 0x40
  xlu 0x1d37  -- 1d36 MLOAD
  xs 0x1d38 (.reg (.swap 0)) (ri_swap (by rfl))  -- 1d37 SWAP1
  xs2 0x1d39 (.reg .sgt) ri_sgt  -- 1d38 SGT
  xs 0x1d3a (.reg .iszero) ri_iszero  -- 1d39 ISZERO
  xs 0x1d3d (.push [0x1d, 0x42] (by decide)) ri_push  -- 1d3a PUSH2 0x1d42
  xji 0x1d3e 0x1d42 hw
  · xdead  -- 1d3d JUMPI
  clear hw
  xjd 0x1d43  -- 1d42 JUMPDEST
  xs 0x1d44 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1d43 DUP1
  xs 0x1d45 (.reg (.swap 1)) (ri_swap (by rfl))  -- 1d44 SWAP2
  xs 0x1d46 (.reg (.swap 0)) (ri_swap (by rfl))  -- 1d45 SWAP1
  xs2 0x1d47 (.reg .slt) ri_slt  -- 1d46 SLT
  xs 0x1d48 (.reg .iszero) ri_iszero  -- 1d47 ISZERO
  xs 0x1d4b (.push [0x1d, 0x50] (by decide)) ri_push  -- 1d48 PUSH2 0x1d50
  xji 0x1d4c 0x1d50 hw
  · xdead  -- 1d4b JUMPI
  clear hw
  xjd 0x1d51  -- 1d50 JUMPDEST
  xs 0x1d52 (.reg .pop) ri_pop  -- 1d51 POP
  xs 0x1d54 (.push [0x60] (by decide)) ri_push  -- 1d52 PUSH1 0x60
  xlu 0x1d55  -- 1d54 MLOAD
  xs 0x1d57 (.push [0x24] (by decide)) ri_push  -- 1d55 PUSH1 0x24
  xs 0x1d58 (.reg .calldataload) ri_calldataload  -- 1d57 CALLDATALOAD
  xs 0x1d59 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1d58 DUP1
  xs 0x1d5b (.push [0x40] (by decide)) ri_push  -- 1d59 PUSH1 0x40
  xlu 0x1d5c  -- 1d5b MLOAD
  xs 0x1d5d (.reg (.swap 0)) (ri_swap (by rfl))  -- 1d5c SWAP1
  xs2 0x1d5e (.reg .sgt) ri_sgt  -- 1d5d SGT
  xs 0x1d5f (.reg .iszero) ri_iszero  -- 1d5e ISZERO
  xs 0x1d62 (.push [0x1d, 0x67] (by decide)) ri_push  -- 1d5f PUSH2 0x1d67
  xji 0x1d63 0x1d67 hw
  · xdead  -- 1d62 JUMPI
  clear hw
  xjd 0x1d68  -- 1d67 JUMPDEST
  xs 0x1d69 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1d68 DUP1
  xs 0x1d6a (.reg (.swap 1)) (ri_swap (by rfl))  -- 1d69 SWAP2
  xs 0x1d6b (.reg (.swap 0)) (ri_swap (by rfl))  -- 1d6a SWAP1
  xs2 0x1d6c (.reg .slt) ri_slt  -- 1d6b SLT
  xs 0x1d6d (.reg .iszero) ri_iszero  -- 1d6c ISZERO
  xs 0x1d70 (.push [0x1d, 0x75] (by decide)) ri_push  -- 1d6d PUSH2 0x1d75
  xji 0x1d71 0x1d75 hw
  · xdead  -- 1d70 JUMPI
  clear hw
  xjd 0x1d76  -- 1d75 JUMPDEST
  xs 0x1d77 (.reg .pop) ri_pop  -- 1d76 POP
  xs 0x1d7a (.push [0x01, 0x40] (by decide)) ri_push  -- 1d77 PUSH2 0x0140
  xs 0x1d83 (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push  -- 1d7a PUSH8 0x0de0b6b3a7640000
  xs 0x1d84 (.reg (.dup 1)) (ri_dup (by rfl))  -- 1d83 DUP2
  xsw 0x1d85 0x140  -- 1d84 MSTORE
  xs 0x1d93 (.push [0x0c, 0x9f, 0x2c, 0x9c, 0xd0, 0x46, 0x74, 0xed, 0xea, 0x40, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 1d85 PUSH13 0x0c9f2c9cd04674edea40000000
  xs 0x1d94 (.reg (.dup 1)) (ri_dup (by rfl))  -- 1d93 DUP2
  xs 0x1d96 (.push [0x20] (by decide)) ri_push  -- 1d94 PUSH1 0x20
  xs 0x1d97 (.reg .add) ri_add  -- 1d96 ADD
  xsw 0x1d98 0x160  -- 1d97 MSTORE
  xs 0x1da6 (.push [0x0c, 0x9f, 0x2c, 0x9c, 0xd0, 0x46, 0x74, 0xed, 0xea, 0x40, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 1d98 PUSH13 0x0c9f2c9cd04674edea40000000
  xs 0x1da7 (.reg (.dup 1)) (ri_dup (by rfl))  -- 1da6 DUP2
  xs 0x1da9 (.push [0x40] (by decide)) ri_push  -- 1da7 PUSH1 0x40
  xs 0x1daa (.reg .add) ri_add  -- 1da9 ADD
  xsw 0x1dab 0x180  -- 1daa MSTORE
  xs 0x1dac (.reg .pop) ri_pop  -- 1dab POP
  xs 0x1daf (.push [0x01, 0xa0] (by decide)) ri_push  -- 1dac PUSH2 0x01a0
  xs 0x1db2 (.push [0x01, 0x40] (by decide)) ri_push  -- 1daf PUSH2 0x0140
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
  xs 0x1dcb (.reg .add) ri_add  -- 1dca ADD
  xs 0x1dce (.push [0x02, 0x81] (by decide)) ri_push  -- 1dcb PUSH2 0x0281
  xjmp 0x281  -- 1dce JUMP
  obtain ⟨x0, x1, x2, b1, M, G1, hb1, h, hx, hV1⟩ := xa_vXp hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x1dd0  -- 1dcf JUMPDEST
  xs 0x1dd3 (.push [0x02, 0x20] (by decide)) ri_push  -- 1dd0 PUSH2 0x0220
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
  xs 0x1df7 (.push [0x02, 0x20] (by decide)) ri_push  -- 1df4 PUSH2 0x0220
  xs 0x1df8 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1df7 DUP1
  xl 0x1df9 0x220  -- 1df8 MLOAD
  xs 0x1dfa (.reg (.dup 2)) (ri_dup (by rfl))  -- 1df9 DUP3
  xsw 0x1dfb 0x1a0  -- 1dfa MSTORE
  xs 0x1dfc (.reg (.dup 0)) (ri_dup (by rfl))  -- 1dfb DUP1
  xs 0x1dfe (.push [0x20] (by decide)) ri_push  -- 1dfc PUSH1 0x20
  xs 0x1dff (.reg .add) ri_add  -- 1dfe ADD
  xl 0x1e00 0x240  -- 1dff MLOAD
  xs 0x1e01 (.reg (.dup 2)) (ri_dup (by rfl))  -- 1e00 DUP3
  xs 0x1e03 (.push [0x20] (by decide)) ri_push  -- 1e01 PUSH1 0x20
  xs 0x1e04 (.reg .add) ri_add  -- 1e03 ADD
  xsw 0x1e05 0x1c0  -- 1e04 MSTORE
  xs 0x1e06 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1e05 DUP1
  xs 0x1e08 (.push [0x40] (by decide)) ri_push  -- 1e06 PUSH1 0x40
  xs 0x1e09 (.reg .add) ri_add  -- 1e08 ADD
  xl 0x1e0a 0x260  -- 1e09 MLOAD
  xs 0x1e0b (.reg (.dup 2)) (ri_dup (by rfl))  -- 1e0a DUP3
  xs 0x1e0d (.push [0x40] (by decide)) ri_push  -- 1e0b PUSH1 0x40
  xs 0x1e0e (.reg .add) ri_add  -- 1e0d ADD
  xsw 0x1e0f 0x1e0  -- 1e0e MSTORE
  xs 0x1e10 (.reg .pop) ri_pop  -- 1e0f POP
  xs 0x1e11 (.reg .pop) ri_pop  -- 1e10 POP
  xs 0x1e14 (.push [0x01, 0xa0] (by decide)) ri_push  -- 1e11 PUSH2 0x01a0
  xs 0x1e16 (.push [0x04] (by decide)) ri_push  -- 1e14 PUSH1 0x04
  xs 0x1e17 (.reg .calldataload) ri_calldataload  -- 1e16 CALLDATALOAD
  xs 0x1e19 (.push [0x03] (by decide)) ri_push  -- 1e17 PUSH1 0x03
  xs 0x1e1a (.reg (.dup 1)) (ri_dup (by rfl))  -- 1e19 DUP2
  xs 0x1e1b (.reg .lt) ri_lt  -- 1e1a LT
  xs 0x1e1e (.push [0x1e, 0x23] (by decide)) ri_push  -- 1e1b PUSH2 0x1e23
  xji 0x1e1f 0x1e23 hw
  · xdead  -- 1e1e JUMPI
  have hi := ltCheck_ne_zero hw
  rw [show (Bytes.toB256 [3]).toNat = 3 from rfl] at hi
  clear hw
  xjd 0x1e24  -- 1e23 JUMPDEST
  xs 0x1e26 (.push [0x20] (by decide)) ri_push  -- 1e24 PUSH1 0x20
  xs 0x1e27 (.reg .mul) ri_mul  -- 1e26 MUL
  xs 0x1e28 (.reg .add) ri_add  -- 1e27 ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1e29) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x1a0) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xs 0x1e2b (.push [0x44] (by decide)) ri_push  -- 1e29 PUSH1 0x44
  xs 0x1e2c (.reg .calldataload) ri_calldataload  -- 1e2b CALLDATALOAD
  xs 0x1e2f (.push [0x01, 0x40] (by decide)) ri_push  -- 1e2c PUSH2 0x0140
  xs 0x1e31 (.push [0x04] (by decide)) ri_push  -- 1e2f PUSH1 0x04
  xs 0x1e32 (.reg .calldataload) ri_calldataload  -- 1e31 CALLDATALOAD
  xs 0x1e34 (.push [0x03] (by decide)) ri_push  -- 1e32 PUSH1 0x03
  xs 0x1e35 (.reg (.dup 1)) (ri_dup (by rfl))  -- 1e34 DUP2
  xs 0x1e36 (.reg .lt) ri_lt  -- 1e35 LT
  xs 0x1e39 (.push [0x1e, 0x3e] (by decide)) ri_push  -- 1e36 PUSH2 0x1e3e
  xji 0x1e3a 0x1e3e hw
  · xdead  -- 1e39 JUMPI
  clear hw
  xjd 0x1e3f  -- 1e3e JUMPDEST
  xs 0x1e41 (.push [0x20] (by decide)) ri_push  -- 1e3f PUSH1 0x20
  xs 0x1e42 (.reg .mul) ri_mul  -- 1e41 MUL
  xs 0x1e43 (.reg .add) ri_add  -- 1e42 ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1e44) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xs 0x1e45 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1e44 DUP1
  xs 0x1e46 (.reg (.dup 2)) (ri_dup (by rfl))  -- 1e45 DUP3
  xs 0x1e47 (.reg .mul) ri_mul  -- 1e46 MUL
  xs 0x1e48 (.reg (.dup 2)) (ri_dup (by rfl))  -- 1e47 DUP3
  xs 0x1e49 (.reg .iszero) ri_iszero  -- 1e48 ISZERO
  xs 0x1e4a (.reg (.dup 2)) (ri_dup (by rfl))  -- 1e49 DUP3
  xs 0x1e4b (.reg (.dup 4)) (ri_dup (by rfl))  -- 1e4a DUP5
  xs 0x1e4c (.reg (.dup 3)) (ri_dup (by rfl))  -- 1e4b DUP4
  xs 0x1e4d (.reg .div) ri_div  -- 1e4c DIV
  xs 0x1e4e (.reg .eq) ri_eq  -- 1e4d EQ
  xs 0x1e4f (.reg .or) ri_or  -- 1e4e OR
  xs 0x1e52 (.push [0x1e, 0x57] (by decide)) ri_push  -- 1e4f PUSH2 0x1e57
  xji 0x1e53 0x1e57 hw
  · xdead  -- 1e52 JUMPI
  have hmx := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x1e58  -- 1e57 JUMPDEST
  xs 0x1e59 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1e58 DUP1
  xs 0x1e5a (.reg (.swap 0)) (ri_swap (by rfl))  -- 1e59 SWAP1
  xs 0x1e5b (.reg .pop) ri_pop  -- 1e5a POP
  xs 0x1e5c (.reg (.swap 0)) (ri_swap (by rfl))  -- 1e5b SWAP1
  xs 0x1e5d (.reg .pop) ri_pop  -- 1e5c POP
  xs 0x1e5e (.reg (.swap 0)) (ri_swap (by rfl))  -- 1e5d SWAP1
  xs 0x1e5f (.reg .pop) ri_pop  -- 1e5e POP
  xs 0x1e68 (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push  -- 1e5f PUSH8 0x0de0b6b3a7640000
  xs 0x1e69 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1e68 DUP1
  xs 0x1e6a (.reg (.dup 0)) (ri_dup (by rfl))  -- 1e69 DUP1
  xs 0x1e6d (.push [0x1e, 0x72] (by decide)) ri_push  -- 1e6a PUSH2 0x1e72
  xji 0x1e6e 0x1e72 hw
  · xdead  -- 1e6d JUMPI
  clear hw
  xjd 0x1e73  -- 1e72 JUMPDEST
  xs 0x1e74 (.reg (.dup 2)) (ri_dup (by rfl))  -- 1e73 DUP3
  xs 0x1e75 (.reg .div) ri_div  -- 1e74 DIV
  xs 0x1e76 (.reg (.swap 0)) (ri_swap (by rfl))  -- 1e75 SWAP1
  xs 0x1e77 (.reg .pop) ri_pop  -- 1e76 POP
  xs 0x1e78 (.reg (.swap 0)) (ri_swap (by rfl))  -- 1e77 SWAP1
  xs 0x1e79 (.reg .pop) ri_pop  -- 1e78 POP
  xs 0x1e7a (.reg (.dup 1)) (ri_dup (by rfl))  -- 1e79 DUP2
  xs 0x1e7b (.reg (.dup 1)) (ri_dup (by rfl))  -- 1e7a DUP2
  xs 0x1e7c (.reg (.dup 3)) (ri_dup (by rfl))  -- 1e7b DUP4
  xs 0x1e7d (.reg .add) ri_add  -- 1e7c ADD
  xs 0x1e7e (.reg .lt) ri_lt  -- 1e7d LT
  xs 0x1e7f (.reg .iszero) ri_iszero  -- 1e7e ISZERO
  xs 0x1e82 (.push [0x1e, 0x87] (by decide)) ri_push  -- 1e7f PUSH2 0x1e87
  xji 0x1e83 0x1e87 hw
  · xdead  -- 1e82 JUMPI
  have hax := (B256.nof_iff_not_add_lt _ _).mpr
    (ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xjd 0x1e88  -- 1e87 JUMPDEST
  xs 0x1e89 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1e88 DUP1
  xs 0x1e8a (.reg (.dup 2)) (ri_dup (by rfl))  -- 1e89 DUP3
  xs 0x1e8b (.reg .add) ri_add  -- 1e8a ADD
  xs 0x1e8c (.reg (.swap 0)) (ri_swap (by rfl))  -- 1e8b SWAP1
  xs 0x1e8d (.reg .pop) ri_pop  -- 1e8c POP
  xs 0x1e8e (.reg (.swap 0)) (ri_swap (by rfl))  -- 1e8d SWAP1
  xs 0x1e8f (.reg .pop) ri_pop  -- 1e8e POP
  xs 0x1e92 (.push [0x02, 0x80] (by decide)) ri_push  -- 1e8f PUSH2 0x0280
  xsw 0x1e93 0x280  -- 1e92 MSTORE
  xs 0x1e96 (.push [0x01, 0x40] (by decide)) ri_push  -- 1e93 PUSH2 0x0140
  xs 0x1e99 (.push [0x02, 0xc0] (by decide)) ri_push  -- 1e96 PUSH2 0x02c0
  xsw 0x1e9a 0x2c0  -- 1e99 MSTORE

  refine ⟨hval, x0, x1, x2, b1, _, _, hb1, hi, hx, hmx, hax, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

-- SEGMENT: dyY
/-- **`get_dy` from the frame save to past the frame restore around `get_y`.** -/
theorem xa_dy_y (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 X : B256}
    {M : Mem} (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hV : VW M [(0x2c0, Bytes.toB256 [1, 64]), (0x280, X), (0x140, rP), (0x160, rQ), (0x180, rQ),
      (0x1a0, x0), (0x1c0, x1), (0x1e0, x2)])
    (h : XAt sevm post 0x1e9a (St b [] M G) L) :
    ∃ (y : B256) (b2 : Devm) (M2 : Mem) (G2 : Nat), SloadsOnly sevm b b2 ∧
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
  xs 0x1ebf (.push [0x04] (by decide)) ri_push  -- 1ebd PUSH1 0x04
  xs 0x1ec0 (.reg .calldataload) ri_calldataload  -- 1ebf CALLDATALOAD
  xs 0x1ec3 (.push [0x02, 0xe0] (by decide)) ri_push  -- 1ec0 PUSH2 0x02e0
  xsw 0x1ec4 0x2e0  -- 1ec3 MSTORE
  xs 0x1ec6 (.push [0x24] (by decide)) ri_push  -- 1ec4 PUSH1 0x24
  xs 0x1ec7 (.reg .calldataload) ri_calldataload  -- 1ec6 CALLDATALOAD
  xs 0x1eca (.push [0x03, 0x00] (by decide)) ri_push  -- 1ec7 PUSH2 0x0300
  xsw 0x1ecb 0x300  -- 1eca MSTORE
  xs 0x1ece (.push [0x02, 0x80] (by decide)) ri_push  -- 1ecb PUSH2 0x0280
  xl 0x1ecf 0x280  -- 1ece MLOAD
  xs 0x1ed2 (.push [0x03, 0x20] (by decide)) ri_push  -- 1ecf PUSH2 0x0320
  xsw 0x1ed3 0x320  -- 1ed2 MSTORE
  xs 0x1ed6 (.push [0x03, 0x40] (by decide)) ri_push  -- 1ed3 PUSH2 0x0340
  xs 0x1ed9 (.push [0x01, 0xa0] (by decide)) ri_push  -- 1ed6 PUSH2 0x01a0
  xs 0x1eda (.reg (.dup 0)) (ri_dup (by rfl))  -- 1ed9 DUP1
  xl 0x1edb 0x1a0  -- 1eda MLOAD
  xs 0x1edc (.reg (.dup 2)) (ri_dup (by rfl))  -- 1edb DUP3
  xsw 0x1edd 0x340  -- 1edc MSTORE
  xs 0x1ede (.reg (.dup 0)) (ri_dup (by rfl))  -- 1edd DUP1
  xs 0x1ee0 (.push [0x20] (by decide)) ri_push  -- 1ede PUSH1 0x20
  xs 0x1ee1 (.reg .add) ri_add  -- 1ee0 ADD
  xl 0x1ee2 0x1c0  -- 1ee1 MLOAD
  xs 0x1ee3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 1ee2 DUP3
  xs 0x1ee5 (.push [0x20] (by decide)) ri_push  -- 1ee3 PUSH1 0x20
  xs 0x1ee6 (.reg .add) ri_add  -- 1ee5 ADD
  xsw 0x1ee7 0x360  -- 1ee6 MSTORE
  xs 0x1ee8 (.reg (.dup 0)) (ri_dup (by rfl))  -- 1ee7 DUP1
  xs 0x1eea (.push [0x40] (by decide)) ri_push  -- 1ee8 PUSH1 0x40
  xs 0x1eeb (.reg .add) ri_add  -- 1eea ADD
  xl 0x1eec 0x1e0  -- 1eeb MLOAD
  xs 0x1eed (.reg (.dup 2)) (ri_dup (by rfl))  -- 1eec DUP3
  xs 0x1eef (.push [0x40] (by decide)) ri_push  -- 1eed PUSH1 0x40
  xs 0x1ef0 (.reg .add) ri_add  -- 1eef ADD
  xsw 0x1ef1 0x380  -- 1ef0 MSTORE
  xs 0x1ef2 (.reg .pop) ri_pop  -- 1ef1 POP
  xs 0x1ef3 (.reg .pop) ri_pop  -- 1ef2 POP
  xs 0x1ef6 (.push [0x03, 0x80] (by decide)) ri_push  -- 1ef3 PUSH2 0x0380
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
  xs 0x1f0f (.reg .add) ri_add  -- 1f0e ADD
  xs 0x1f12 (.push [0x18, 0xa4] (by decide)) ri_push  -- 1f0f PUSH2 0x18a4
  xjmp 0x18a4  -- 1f12 JUMP
  obtain ⟨y, M3, _, h, amp, hamp, hi, hj, hy, hV1⟩ := xa_vGetY hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x1f14  -- 1f13 JUMPDEST
  xs 0x1f17 (.push [0x03, 0xe0] (by decide)) ri_push  -- 1f14 PUSH2 0x03e0
  xsw 0x1f18 0x3e0  -- 1f17 MSTORE
  xs 0x1f1b (.push [0x02, 0xa0] (by decide)) ri_push  -- 1f18 PUSH2 0x02a0
  xs 0x1f1e (.push [0x02, 0xc0] (by decide)) ri_push  -- 1f1b PUSH2 0x02c0
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
  refine ⟨y, _, M4, _, aBase_sloadsOnly sevm b, h, amp, hamp, hi, hj, hy, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_append, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
