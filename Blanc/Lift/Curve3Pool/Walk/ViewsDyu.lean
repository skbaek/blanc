import Blanc.Lift.Curve3Pool.Walk.ViewsDyPost

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
  xs 0x2055 (.reg .callvalue) ri_callvalue  -- 2054 CALLVALUE
  xs 0x2056 (.reg .iszero) ri_iszero  -- 2055 ISZERO
  xs 0x2059 (.push [0x20, 0x5e] (by decide)) ri_push  -- 2056 PUSH2 0x205e
  xji 0x205a 0x205e hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x205f  -- 205e JUMPDEST
  xs 0x2061 (.push [0x60] (by decide)) ri_push  -- 205f PUSH1 0x60
  xlu 0x2062  -- 2061 MLOAD
  xs 0x2064 (.push [0x04] (by decide)) ri_push  -- 2062 PUSH1 0x04
  xs 0x2065 (.reg .calldataload) ri_calldataload  -- 2064 CALLDATALOAD
  xs 0x2066 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2065 DUP1
  xs 0x2068 (.push [0x40] (by decide)) ri_push  -- 2066 PUSH1 0x40
  xlu 0x2069  -- 2068 MLOAD
  xs 0x206a (.reg (.swap 0)) (ri_swap (by rfl))  -- 2069 SWAP1
  xs2 0x206b (.reg .sgt) ri_sgt  -- 206a SGT
  xs 0x206c (.reg .iszero) ri_iszero  -- 206b ISZERO
  xs 0x206f (.push [0x20, 0x74] (by decide)) ri_push  -- 206c PUSH2 0x2074
  xji 0x2070 0x2074 hw
  · xdead
  clear hw
  xjd 0x2075  -- 2074 JUMPDEST
  xs 0x2076 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2075 DUP1
  xs 0x2077 (.reg (.swap 1)) (ri_swap (by rfl))  -- 2076 SWAP2
  xs 0x2078 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2077 SWAP1
  xs2 0x2079 (.reg .slt) ri_slt  -- 2078 SLT
  xs 0x207a (.reg .iszero) ri_iszero  -- 2079 ISZERO
  xs 0x207d (.push [0x20, 0x82] (by decide)) ri_push  -- 207a PUSH2 0x2082
  xji 0x207e 0x2082 hw
  · xdead
  clear hw
  xjd 0x2083  -- 2082 JUMPDEST
  xs 0x2084 (.reg .pop) ri_pop  -- 2083 POP
  xs 0x2086 (.push [0x60] (by decide)) ri_push  -- 2084 PUSH1 0x60
  xlu 0x2087  -- 2086 MLOAD
  xs 0x2089 (.push [0x24] (by decide)) ri_push  -- 2087 PUSH1 0x24
  xs 0x208a (.reg .calldataload) ri_calldataload  -- 2089 CALLDATALOAD
  xs 0x208b (.reg (.dup 0)) (ri_dup (by rfl))  -- 208a DUP1
  xs 0x208d (.push [0x40] (by decide)) ri_push  -- 208b PUSH1 0x40
  xlu 0x208e  -- 208d MLOAD
  xs 0x208f (.reg (.swap 0)) (ri_swap (by rfl))  -- 208e SWAP1
  xs2 0x2090 (.reg .sgt) ri_sgt  -- 208f SGT
  xs 0x2091 (.reg .iszero) ri_iszero  -- 2090 ISZERO
  xs 0x2094 (.push [0x20, 0x99] (by decide)) ri_push  -- 2091 PUSH2 0x2099
  xji 0x2095 0x2099 hw
  · xdead
  clear hw
  xjd 0x209a  -- 2099 JUMPDEST
  xs 0x209b (.reg (.dup 0)) (ri_dup (by rfl))  -- 209a DUP1
  xs 0x209c (.reg (.swap 1)) (ri_swap (by rfl))  -- 209b SWAP2
  xs 0x209d (.reg (.swap 0)) (ri_swap (by rfl))  -- 209c SWAP1
  xs2 0x209e (.reg .slt) ri_slt  -- 209d SLT
  xs 0x209f (.reg .iszero) ri_iszero  -- 209e ISZERO
  xs 0x20a2 (.push [0x20, 0xa7] (by decide)) ri_push  -- 209f PUSH2 0x20a7
  xji 0x20a3 0x20a7 hw
  · xdead
  clear hw
  xjd 0x20a8  -- 20a7 JUMPDEST
  xs 0x20a9 (.reg .pop) ri_pop  -- 20a8 POP
  xs 0x20ac (.push [0x01, 0x40] (by decide)) ri_push  -- 20a9 PUSH2 0x0140
  xs 0x20af (.push [0x01, 0x40] (by decide)) ri_push  -- 20ac PUSH2 0x0140
  xlu 0x20b0  -- 20af MLOAD
  xs 0x20b3 (.push [0x01, 0x60] (by decide)) ri_push  -- 20b0 PUSH2 0x0160
  xlu 0x20b4  -- 20b3 MLOAD
  xs 0x20b7 (.push [0x01, 0x80] (by decide)) ri_push  -- 20b4 PUSH2 0x0180
  xlu 0x20b8  -- 20b7 MLOAD
  xs 0x20ba (.push [0x06] (by decide)) ri_push  -- 20b8 PUSH1 0x06
  cvpc 0x20bb  -- 20ba PC
  xs 0x20bc (.reg .add) ri_add  -- 20bb ADD
  xs 0x20bf (.push [0x02, 0x81] (by decide)) ri_push  -- 20bc PUSH2 0x0281
  xjmp 0x281  -- 20bf JUMP
  obtain ⟨x0, x1, x2, b1, M, G1, hb1, h, hx, hV1⟩ := xa_vXp hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x20c1  -- 20c0 JUMPDEST
  xs 0x20c4 (.push [0x01, 0xc0] (by decide)) ri_push  -- 20c1 PUSH2 0x01c0
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
  xs 0x20dc (.push [0x01, 0xc0] (by decide)) ri_push  -- 20d9 PUSH2 0x01c0
  xs 0x20dd (.reg (.dup 0)) (ri_dup (by rfl))  -- 20dc DUP1
  xl 0x20de 0x1c0  -- 20dd MLOAD
  xs 0x20df (.reg (.dup 2)) (ri_dup (by rfl))  -- 20de DUP3
  xsw 0x20e0 0x140  -- 20df MSTORE
  xs 0x20e1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 20e0 DUP1
  xs 0x20e3 (.push [0x20] (by decide)) ri_push  -- 20e1 PUSH1 0x20
  xs 0x20e4 (.reg .add) ri_add  -- 20e3 ADD
  xl 0x20e5 0x1e0  -- 20e4 MLOAD
  xs 0x20e6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 20e5 DUP3
  xs 0x20e8 (.push [0x20] (by decide)) ri_push  -- 20e6 PUSH1 0x20
  xs 0x20e9 (.reg .add) ri_add  -- 20e8 ADD
  xsw 0x20ea 0x160  -- 20e9 MSTORE
  xs 0x20eb (.reg (.dup 0)) (ri_dup (by rfl))  -- 20ea DUP1
  xs 0x20ed (.push [0x40] (by decide)) ri_push  -- 20eb PUSH1 0x40
  xs 0x20ee (.reg .add) ri_add  -- 20ed ADD
  xl 0x20ef 0x200  -- 20ee MLOAD
  xs 0x20f0 (.reg (.dup 2)) (ri_dup (by rfl))  -- 20ef DUP3
  xs 0x20f2 (.push [0x40] (by decide)) ri_push  -- 20f0 PUSH1 0x40
  xs 0x20f3 (.reg .add) ri_add  -- 20f2 ADD
  xsw 0x20f4 0x180  -- 20f3 MSTORE
  xs 0x20f5 (.reg .pop) ri_pop  -- 20f4 POP
  xs 0x20f6 (.reg .pop) ri_pop  -- 20f5 POP
  xs 0x20f9 (.push [0x02, 0x20] (by decide)) ri_push  -- 20f6 PUSH2 0x0220
  xs 0x20fb (.push [0x01] (by decide)) ri_push  -- 20f9 PUSH1 0x01
  xs 0x20fc (.reg (.dup 1)) (ri_dup (by rfl))  -- 20fb DUP2
  xsw 0x20fd 0x220  -- 20fc MSTORE
  xs 0x2103 (.push [0xe8, 0xd4, 0xa5, 0x10, 0x00] (by decide)) ri_push  -- 20fd PUSH5 0xe8d4a51000
  xs 0x2104 (.reg (.dup 1)) (ri_dup (by rfl))  -- 2103 DUP2
  xs 0x2106 (.push [0x20] (by decide)) ri_push  -- 2104 PUSH1 0x20
  xs 0x2107 (.reg .add) ri_add  -- 2106 ADD
  xsw 0x2108 0x240  -- 2107 MSTORE
  xs 0x210e (.push [0xe8, 0xd4, 0xa5, 0x10, 0x00] (by decide)) ri_push  -- 2108 PUSH5 0xe8d4a51000
  xs 0x210f (.reg (.dup 1)) (ri_dup (by rfl))  -- 210e DUP2
  xs 0x2111 (.push [0x40] (by decide)) ri_push  -- 210f PUSH1 0x40
  xs 0x2112 (.reg .add) ri_add  -- 2111 ADD
  xsw 0x2113 0x260  -- 2112 MSTORE
  xs 0x2114 (.reg .pop) ri_pop  -- 2113 POP
  xs 0x2117 (.push [0x01, 0x40] (by decide)) ri_push  -- 2114 PUSH2 0x0140
  xs 0x2119 (.push [0x04] (by decide)) ri_push  -- 2117 PUSH1 0x04
  xs 0x211a (.reg .calldataload) ri_calldataload  -- 2119 CALLDATALOAD
  xs 0x211c (.push [0x03] (by decide)) ri_push  -- 211a PUSH1 0x03
  xs 0x211d (.reg (.dup 1)) (ri_dup (by rfl))  -- 211c DUP2
  xs 0x211e (.reg .lt) ri_lt  -- 211d LT
  xs 0x2121 (.push [0x21, 0x26] (by decide)) ri_push  -- 211e PUSH2 0x2126
  xji 0x2122 0x2126 hw
  · xdead
  have hi := ltCheck_ne_zero hw
  rw [show (Bytes.toB256 [3]).toNat = 3 from rfl] at hi
  clear hw
  xjd 0x2127  -- 2126 JUMPDEST
  xs 0x2129 (.push [0x20] (by decide)) ri_push  -- 2127 PUSH1 0x20
  xs 0x212a (.reg .mul) ri_mul  -- 2129 MUL
  xs 0x212b (.reg .add) ri_add  -- 212a ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x212c) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xs 0x212e (.push [0x44] (by decide)) ri_push  -- 212c PUSH1 0x44
  xs 0x212f (.reg .calldataload) ri_calldataload  -- 212e CALLDATALOAD
  xs 0x2132 (.push [0x02, 0x20] (by decide)) ri_push  -- 212f PUSH2 0x0220
  xs 0x2134 (.push [0x04] (by decide)) ri_push  -- 2132 PUSH1 0x04
  xs 0x2135 (.reg .calldataload) ri_calldataload  -- 2134 CALLDATALOAD
  xs 0x2137 (.push [0x03] (by decide)) ri_push  -- 2135 PUSH1 0x03
  xs 0x2138 (.reg (.dup 1)) (ri_dup (by rfl))  -- 2137 DUP2
  xs 0x2139 (.reg .lt) ri_lt  -- 2138 LT
  xs 0x213c (.push [0x21, 0x41] (by decide)) ri_push  -- 2139 PUSH2 0x2141
  xji 0x213d 0x2141 hw
  · xdead
  clear hw
  xjd 0x2142  -- 2141 JUMPDEST
  xs 0x2144 (.push [0x20] (by decide)) ri_push  -- 2142 PUSH1 0x20
  xs 0x2145 (.reg .mul) ri_mul  -- 2144 MUL
  xs 0x2146 (.reg .add) ri_add  -- 2145 ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x2147) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) s
  clear s
  xs 0x2148 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2147 DUP1
  xs 0x2149 (.reg (.dup 2)) (ri_dup (by rfl))  -- 2148 DUP3
  xs 0x214a (.reg .mul) ri_mul  -- 2149 MUL
  xs 0x214b (.reg (.dup 2)) (ri_dup (by rfl))  -- 214a DUP3
  xs 0x214c (.reg .iszero) ri_iszero  -- 214b ISZERO
  xs 0x214d (.reg (.dup 2)) (ri_dup (by rfl))  -- 214c DUP3
  xs 0x214e (.reg (.dup 4)) (ri_dup (by rfl))  -- 214d DUP5
  xs 0x214f (.reg (.dup 3)) (ri_dup (by rfl))  -- 214e DUP4
  xs 0x2150 (.reg .div) ri_div  -- 214f DIV
  xs 0x2151 (.reg .eq) ri_eq  -- 2150 EQ
  xs 0x2152 (.reg .or) ri_or  -- 2151 OR
  xs 0x2155 (.push [0x21, 0x5a] (by decide)) ri_push  -- 2152 PUSH2 0x215a
  xji 0x2156 0x215a hw
  · xdead
  have hmx := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x215b  -- 215a JUMPDEST
  xs 0x215c (.reg (.dup 0)) (ri_dup (by rfl))  -- 215b DUP1
  xs 0x215d (.reg (.swap 0)) (ri_swap (by rfl))  -- 215c SWAP1
  xs 0x215e (.reg .pop) ri_pop  -- 215d POP
  xs 0x215f (.reg (.swap 0)) (ri_swap (by rfl))  -- 215e SWAP1
  xs 0x2160 (.reg .pop) ri_pop  -- 215f POP
  xs 0x2161 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2160 SWAP1
  xs 0x2162 (.reg .pop) ri_pop  -- 2161 POP
  xs 0x2163 (.reg (.dup 1)) (ri_dup (by rfl))  -- 2162 DUP2
  xs 0x2164 (.reg (.dup 1)) (ri_dup (by rfl))  -- 2163 DUP2
  xs 0x2165 (.reg (.dup 3)) (ri_dup (by rfl))  -- 2164 DUP4
  xs 0x2166 (.reg .add) ri_add  -- 2165 ADD
  xs 0x2167 (.reg .lt) ri_lt  -- 2166 LT
  xs 0x2168 (.reg .iszero) ri_iszero  -- 2167 ISZERO
  xs 0x216b (.push [0x21, 0x70] (by decide)) ri_push  -- 2168 PUSH2 0x2170
  xji 0x216c 0x2170 hw
  · xdead
  have hax := (B256.nof_iff_not_add_lt _ _).mpr
    (ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xjd 0x2171  -- 2170 JUMPDEST
  xs 0x2172 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2171 DUP1
  xs 0x2173 (.reg (.dup 2)) (ri_dup (by rfl))  -- 2172 DUP3
  xs 0x2174 (.reg .add) ri_add  -- 2173 ADD
  xs 0x2175 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2174 SWAP1
  xs 0x2176 (.reg .pop) ri_pop  -- 2175 POP
  xs 0x2177 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2176 SWAP1
  xs 0x2178 (.reg .pop) ri_pop  -- 2177 POP
  xs 0x217b (.push [0x02, 0x80] (by decide)) ri_push  -- 2178 PUSH2 0x0280
  xsw 0x217c 0x280  -- 217b MSTORE
  xs 0x217f (.push [0x01, 0x40] (by decide)) ri_push  -- 217c PUSH2 0x0140
  xs 0x2182 (.push [0x02, 0xc0] (by decide)) ri_push  -- 217f PUSH2 0x02c0
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
  xs 0x21a8 (.push [0x04] (by decide)) ri_push  -- 21a6 PUSH1 0x04
  xs 0x21a9 (.reg .calldataload) ri_calldataload  -- 21a8 CALLDATALOAD
  xs 0x21ac (.push [0x02, 0xe0] (by decide)) ri_push  -- 21a9 PUSH2 0x02e0
  xsw 0x21ad 0x2e0  -- 21ac MSTORE
  xs 0x21af (.push [0x24] (by decide)) ri_push  -- 21ad PUSH1 0x24
  xs 0x21b0 (.reg .calldataload) ri_calldataload  -- 21af CALLDATALOAD
  xs 0x21b3 (.push [0x03, 0x00] (by decide)) ri_push  -- 21b0 PUSH2 0x0300
  xsw 0x21b4 0x300  -- 21b3 MSTORE
  xs 0x21b7 (.push [0x02, 0x80] (by decide)) ri_push  -- 21b4 PUSH2 0x0280
  xl 0x21b8 0x280  -- 21b7 MLOAD
  xs 0x21bb (.push [0x03, 0x20] (by decide)) ri_push  -- 21b8 PUSH2 0x0320
  xsw 0x21bc 0x320  -- 21bb MSTORE
  xs 0x21bf (.push [0x03, 0x40] (by decide)) ri_push  -- 21bc PUSH2 0x0340
  xs 0x21c2 (.push [0x01, 0x40] (by decide)) ri_push  -- 21bf PUSH2 0x0140
  xs 0x21c3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 21c2 DUP1
  xl 0x21c4 0x140  -- 21c3 MLOAD
  xs 0x21c5 (.reg (.dup 2)) (ri_dup (by rfl))  -- 21c4 DUP3
  xsw 0x21c6 0x340  -- 21c5 MSTORE
  xs 0x21c7 (.reg (.dup 0)) (ri_dup (by rfl))  -- 21c6 DUP1
  xs 0x21c9 (.push [0x20] (by decide)) ri_push  -- 21c7 PUSH1 0x20
  xs 0x21ca (.reg .add) ri_add  -- 21c9 ADD
  xl 0x21cb 0x160  -- 21ca MLOAD
  xs 0x21cc (.reg (.dup 2)) (ri_dup (by rfl))  -- 21cb DUP3
  xs 0x21ce (.push [0x20] (by decide)) ri_push  -- 21cc PUSH1 0x20
  xs 0x21cf (.reg .add) ri_add  -- 21ce ADD
  xsw 0x21d0 0x360  -- 21cf MSTORE
  xs 0x21d1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 21d0 DUP1
  xs 0x21d3 (.push [0x40] (by decide)) ri_push  -- 21d1 PUSH1 0x40
  xs 0x21d4 (.reg .add) ri_add  -- 21d3 ADD
  xl 0x21d5 0x180  -- 21d4 MLOAD
  xs 0x21d6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 21d5 DUP3
  xs 0x21d8 (.push [0x40] (by decide)) ri_push  -- 21d6 PUSH1 0x40
  xs 0x21d9 (.reg .add) ri_add  -- 21d8 ADD
  xsw 0x21da 0x380  -- 21d9 MSTORE
  xs 0x21db (.reg .pop) ri_pop  -- 21da POP
  xs 0x21dc (.reg .pop) ri_pop  -- 21db POP
  xs 0x21df (.push [0x03, 0x80] (by decide)) ri_push  -- 21dc PUSH2 0x0380
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
  xs 0x21f8 (.reg .add) ri_add  -- 21f7 ADD
  xs 0x21fb (.push [0x18, 0xa4] (by decide)) ri_push  -- 21f8 PUSH2 0x18a4
  xjmp 0x18a4  -- 21fb JUMP
  obtain ⟨y, M3, _, h, amp, hamp, hi, hj, hy, hV1⟩ := xa_vGetY hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x21fd  -- 21fc JUMPDEST
  xs 0x2200 (.push [0x03, 0xe0] (by decide)) ri_push  -- 21fd PUSH2 0x03e0
  xsw 0x2201 0x3e0  -- 2200 MSTORE
  xs 0x2204 (.push [0x02, 0xa0] (by decide)) ri_push  -- 2201 PUSH2 0x02a0
  xs 0x2207 (.push [0x02, 0xc0] (by decide)) ri_push  -- 2204 PUSH2 0x02c0
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
