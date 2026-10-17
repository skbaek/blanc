import Blanc.Lift.Curve3Pool.Walk.ViewsDyu

/-! # The checked arithmetic and return suffix of `get_dy_underlying` -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

abbrev dyuPj (sevm : Sevm) : B256 := pickWord3 (dyJ sevm).toNat dyuP1 dyuPm dyuPm
abbrev dyuAmount (sevm : Sevm) (x0 x1 x2 y : B256) : B256 :=
  (dyJxp sevm x0 x1 x2 - y - Bytes.toB256 [1]) / dyuPj sevm
abbrev dyuFee (sevm : Sevm) (b : Devm) (x0 x1 x2 y : B256) : B256 :=
  (b.getStorVal sevm.currentTarget (Bytes.toB256 [2])) * dyuAmount sevm x0 x1 x2 y /
    Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]

/-- `get_dy_underlying`'s suffix reads every arithmetic guard and returns the exact net amount. -/
theorem xa_dyu_post {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    {M : Mem} {x0 x1 x2 y : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hj : (dyJ sevm).toNat < 3)
    (hV : VW M [(0x3e0, y), (0x140, x0), (0x160, x1), (0x180, x2), (0x220, dyuP1),
      (0x240, dyuPm), (0x260, dyuPm)])
    (h : XAt sevm post 0x222c (St b [] M G) L) :
    L = [] ∧ y.toNat ≤ (dyJxp sevm x0 x1 x2).toNat ∧
      (Bytes.toB256 [1]).toNat ≤ (dyJxp sevm x0 x1 x2 - y).toNat ∧ dyuPj sevm ≠ 0 ∧
      B256.Nofm (b.getStorVal sevm.currentTarget (Bytes.toB256 [2]))
        (dyuAmount sevm x0 x1 x2 y) ∧
      (dyuFee sevm b x0 x1 x2 y).toNat ≤ (dyuAmount sevm x0 x1 x2 y).toNat ∧
      (∀ a, post.getStor a = b.getStor a) ∧ post.logs = b.logs ∧
      post.output = (dyuAmount sevm x0 x1 x2 y - dyuFee sevm b x0 x1 x2 y).toBytes := by
  xs 0x222f (.push [0x03, 0xe0] (by decide)) ri_push  -- 222c PUSH2 0x03e0
  xl 0x2230 0x3e0  -- 222f MLOAD
  xs 0x2233 (.push [0x02, 0xa0] (by decide)) ri_push  -- 2230 PUSH2 0x02a0
  xsw 0x2234 0x2a0  -- 2233 MSTORE
  xs 0x2237 (.push [0x01, 0x40] (by decide)) ri_push  -- 2234 PUSH2 0x0140
  xs 0x2239 (.push [0x24] (by decide)) ri_push  -- 2237 PUSH1 0x24
  xs 0x223a (.reg .calldataload) ri_calldataload  -- 2239 CALLDATALOAD
  xs 0x223c (.push [0x03] (by decide)) ri_push  -- 223a PUSH1 0x03
  xs 0x223d (.reg (.dup 1)) (ri_dup (by rfl))  -- 223c DUP2
  xs 0x223e (.reg .lt) ri_lt  -- 223d LT
  xs 0x2241 (.push [0x22, 0x46] (by decide)) ri_push  -- 223e PUSH2 0x2246
  xji 0x2242 0x2246 hw
  · xdead
  clear hw
  xjd 0x2247  -- 2246 JUMPDEST
  xs 0x2249 (.push [0x20] (by decide)) ri_push  -- 2247 PUSH1 0x20
  xs 0x224a (.reg .mul) ri_mul  -- 2249 MUL
  xs 0x224b (.reg .add) ri_add  -- 224a ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x224c) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xs 0x224f (.push [0x02, 0xa0] (by decide)) ri_push  -- 224c PUSH2 0x02a0
  xl 0x2250 0x2a0  -- 224f MLOAD
  xs 0x2251 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2250 DUP1
  xs 0x2252 (.reg (.dup 2)) (ri_dup (by rfl))  -- 2251 DUP3
  xs 0x2253 (.reg .lt) ri_lt  -- 2252 LT
  xs 0x2254 (.reg .iszero) ri_iszero  -- 2253 ISZERO
  xs 0x2257 (.push [0x22, 0x5c] (by decide)) ri_push  -- 2254 PUSH2 0x225c
  xji 0x2258 0x225c hw
  · xdead
  have hsub0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x225d  -- 225c JUMPDEST
  xs 0x225e (.reg (.dup 0)) (ri_dup (by rfl))  -- 225d DUP1
  xs 0x225f (.reg (.dup 2)) (ri_dup (by rfl))  -- 225e DUP3
  xs 0x2260 (.reg .sub) ri_sub  -- 225f SUB
  xs 0x2261 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2260 SWAP1
  xs 0x2262 (.reg .pop) ri_pop  -- 2261 POP
  xs 0x2263 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2262 SWAP1
  xs 0x2264 (.reg .pop) ri_pop  -- 2263 POP
  xs 0x2266 (.push [0x01] (by decide)) ri_push  -- 2264 PUSH1 0x01
  xs 0x2267 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2266 DUP1
  xs 0x2268 (.reg (.dup 2)) (ri_dup (by rfl))  -- 2267 DUP3
  xs 0x2269 (.reg .lt) ri_lt  -- 2268 LT
  xs 0x226a (.reg .iszero) ri_iszero  -- 2269 ISZERO
  xs 0x226d (.push [0x22, 0x72] (by decide)) ri_push  -- 226a PUSH2 0x2272
  xji 0x226e 0x2272 hw
  · xdead
  have hsub1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x2273  -- 2272 JUMPDEST
  xs 0x2274 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2273 DUP1
  xs 0x2275 (.reg (.dup 2)) (ri_dup (by rfl))  -- 2274 DUP3
  xs 0x2276 (.reg .sub) ri_sub  -- 2275 SUB
  xs 0x2277 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2276 SWAP1
  xs 0x2278 (.reg .pop) ri_pop  -- 2277 POP
  xs 0x2279 (.reg (.swap 0)) (ri_swap (by rfl))  -- 2278 SWAP1
  xs 0x227a (.reg .pop) ri_pop  -- 2279 POP
  xs 0x227d (.push [0x02, 0x20] (by decide)) ri_push  -- 227a PUSH2 0x0220
  xs 0x227f (.push [0x24] (by decide)) ri_push  -- 227d PUSH1 0x24
  xs 0x2280 (.reg .calldataload) ri_calldataload  -- 227f CALLDATALOAD
  xs 0x2282 (.push [0x03] (by decide)) ri_push  -- 2280 PUSH1 0x03
  xs 0x2283 (.reg (.dup 1)) (ri_dup (by rfl))  -- 2282 DUP2
  xs 0x2284 (.reg .lt) ri_lt  -- 2283 LT
  xs 0x2287 (.push [0x22, 0x8c] (by decide)) ri_push  -- 2284 PUSH2 0x228c
  xji 0x2288 0x228c hw
  · xdead
  clear hw
  xjd 0x228d  -- 228c JUMPDEST
  xs 0x228f (.push [0x20] (by decide)) ri_push  -- 228d PUSH1 0x20
  xs 0x2290 (.reg .mul) ri_mul  -- 228f MUL
  xs 0x2291 (.reg .add) ri_add  -- 2290 ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x2292) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xs 0x2293 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2292 DUP1
  xs 0x2294 (.reg (.dup 0)) (ri_dup (by rfl))  -- 2293 DUP1
  xs 0x2297 (.push [0x22, 0x9c] (by decide)) ri_push  -- 2294 PUSH2 0x229c
  xji 0x2298 0x229c hw
  · xdead
  have hrate := hw
  clear hw
  xjd 0x229d  -- 229c JUMPDEST
  xs 0x229e (.reg (.dup 2)) (ri_dup (by rfl))  -- 229d DUP3
  xs 0x229f (.reg .div) ri_div  -- 229e DIV
  xs 0x22a0 (.reg (.swap 0)) (ri_swap (by rfl))  -- 229f SWAP1
  xs 0x22a1 (.reg .pop) ri_pop  -- 22a0 POP
  xs 0x22a2 (.reg (.swap 0)) (ri_swap (by rfl))  -- 22a1 SWAP1
  xs 0x22a3 (.reg .pop) ri_pop  -- 22a2 POP
  xs 0x22a6 (.push [0x04, 0x00] (by decide)) ri_push  -- 22a3 PUSH2 0x0400
  xsw 0x22a7 0x400  -- 22a6 MSTORE
  xs 0x22a9 (.push [0x02] (by decide)) ri_push  -- 22a7 PUSH1 0x02
  xw 0x22aa (.reg .sload) ri_sload  -- 22a9 SLOAD
  xs 0x22ad (.push [0x04, 0x00] (by decide)) ri_push  -- 22aa PUSH2 0x0400
  xl 0x22ae 0x400  -- 22ad MLOAD
  xs 0x22af (.reg (.dup 0)) (ri_dup (by rfl))  -- 22ae DUP1
  xs 0x22b0 (.reg (.dup 2)) (ri_dup (by rfl))  -- 22af DUP3
  xs 0x22b1 (.reg .mul) ri_mul  -- 22b0 MUL
  xs 0x22b2 (.reg (.dup 2)) (ri_dup (by rfl))  -- 22b1 DUP3
  xs 0x22b3 (.reg .iszero) ri_iszero  -- 22b2 ISZERO
  xs 0x22b4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 22b3 DUP3
  xs 0x22b5 (.reg (.dup 4)) (ri_dup (by rfl))  -- 22b4 DUP5
  xs 0x22b6 (.reg (.dup 3)) (ri_dup (by rfl))  -- 22b5 DUP4
  xs 0x22b7 (.reg .div) ri_div  -- 22b6 DIV
  xs 0x22b8 (.reg .eq) ri_eq  -- 22b7 EQ
  xs 0x22b9 (.reg .or) ri_or  -- 22b8 OR
  xs 0x22bc (.push [0x22, 0xc1] (by decide)) ri_push  -- 22b9 PUSH2 0x22c1
  xji 0x22bd 0x22c1 hw
  · xdead
  have hmul1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x22c2  -- 22c1 JUMPDEST
  xs 0x22c3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 22c2 DUP1
  xs 0x22c4 (.reg (.swap 0)) (ri_swap (by rfl))  -- 22c3 SWAP1
  xs 0x22c5 (.reg .pop) ri_pop  -- 22c4 POP
  xs 0x22c6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 22c5 SWAP1
  xs 0x22c7 (.reg .pop) ri_pop  -- 22c6 POP
  xs 0x22c8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 22c7 SWAP1
  xs 0x22c9 (.reg .pop) ri_pop  -- 22c8 POP
  xs 0x22cf (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 22c9 PUSH5 0x02540be400
  xs 0x22d0 (.reg (.dup 0)) (ri_dup (by rfl))  -- 22cf DUP1
  xs 0x22d1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 22d0 DUP1
  xs 0x22d4 (.push [0x22, 0xd9] (by decide)) ri_push  -- 22d1 PUSH2 0x22d9
  xji 0x22d5 0x22d9 hw
  · xdead
  clear hw
  xjd 0x22da  -- 22d9 JUMPDEST
  xs 0x22db (.reg (.dup 2)) (ri_dup (by rfl))  -- 22da DUP3
  xs 0x22dc (.reg .div) ri_div  -- 22db DIV
  xs 0x22dd (.reg (.swap 0)) (ri_swap (by rfl))  -- 22dc SWAP1
  xs 0x22de (.reg .pop) ri_pop  -- 22dd POP
  xs 0x22df (.reg (.swap 0)) (ri_swap (by rfl))  -- 22de SWAP1
  xs 0x22e0 (.reg .pop) ri_pop  -- 22df POP
  xs 0x22e3 (.push [0x04, 0x20] (by decide)) ri_push  -- 22e0 PUSH2 0x0420
  xsw 0x22e4 0x420  -- 22e3 MSTORE
  xs 0x22e7 (.push [0x04, 0x00] (by decide)) ri_push  -- 22e4 PUSH2 0x0400
  xl 0x22e8 0x400  -- 22e7 MLOAD
  xs 0x22eb (.push [0x04, 0x20] (by decide)) ri_push  -- 22e8 PUSH2 0x0420
  xl 0x22ec 0x420  -- 22eb MLOAD
  xs 0x22ed (.reg (.dup 0)) (ri_dup (by rfl))  -- 22ec DUP1
  xs 0x22ee (.reg (.dup 2)) (ri_dup (by rfl))  -- 22ed DUP3
  xs 0x22ef (.reg .lt) ri_lt  -- 22ee LT
  xs 0x22f0 (.reg .iszero) ri_iszero  -- 22ef ISZERO
  xs 0x22f3 (.push [0x22, 0xf8] (by decide)) ri_push  -- 22f0 PUSH2 0x22f8
  xji 0x22f4 0x22f8 hw
  · xdead
  have hsub2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x22f9  -- 22f8 JUMPDEST
  xs 0x22fa (.reg (.dup 0)) (ri_dup (by rfl))  -- 22f9 DUP1
  xs 0x22fb (.reg (.dup 2)) (ri_dup (by rfl))  -- 22fa DUP3
  xs 0x22fc (.reg .sub) ri_sub  -- 22fb SUB
  xs 0x22fd (.reg (.swap 0)) (ri_swap (by rfl))  -- 22fc SWAP1
  xs 0x22fe (.reg .pop) ri_pop  -- 22fd POP
  xs 0x22ff (.reg (.swap 0)) (ri_swap (by rfl))  -- 22fe SWAP1
  xs 0x2300 (.reg .pop) ri_pop  -- 22ff POP
  xs 0x2302 (.push [0x00] (by decide)) ri_push  -- 2300 PUSH1 0x00
  have hfinalwf := hV.wf
  xsw 0x2303 0x0  -- 2302 MSTORE
  xs 0x2305 (.push [0x20] (by decide)) ri_push  -- 2303 PUSH1 0x20
  xs 0x2307 (.push [0x00] (by decide)) ri_push  -- 2305 PUSH1 0x00
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨rfl, hsub0, hsub1, hrate, hmul1, hsub2,
    fun a => by rw [hstor, afterSload_getStor], by rw [hlogs, afterSload_logs], ?_⟩
  rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl, Mem.read_write_word_of_wf hfinalwf]

end Blanc.Lift.Curve3Pool
