import Blanc.Lift.Curve3Pool.Walk.ViewsCtaD1
import Blanc.Lift.Curve3Pool.Walk.ViewsGvp

/-! # `calc_token_amount`'s suffix: `totalSupply()`, the difference, `diff · supply / D0` -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

-- SEGMENT: ctaFin
/-- **From the joined difference (`0xe03`) to the `RETURN`**: the checked `diff · supply`, the
nonzero `D0`, the output `diff · supply / D0`. -/
theorem xa_cta_fin {M : Mem} {df T D0 : B256}
    (hcode : sevm.code = code) (hV : VW M [(0x500, df), (0x460, T), (0x200, D0)])
    (h : XAt sevm post 0xe03 (St b [] M G) L) :
    L = [] ∧ B256.Nofm df T ∧ D0 ≠ 0 ∧ (∀ a, post.getStor a = b.getStor a) ∧
      post.logs = b.logs ∧ post.output = (df * T / D0).toBytes := by
  xjd 0xe04  -- e03 JUMPDEST
  xs 0xe07 (.push [0x05, 0x00] (by decide)) ri_push  -- e04 PUSH2 0x0500
  xl 0xe08 0x500  -- e07 MLOAD
  xs 0xe0b (.push [0x04, 0x60] (by decide)) ri_push  -- e08 PUSH2 0x0460
  xl 0xe0c 0x460  -- e0b MLOAD
  xs 0xe0d (.reg (.dup 0)) (ri_dup (by rfl))  -- e0c DUP1
  xs 0xe0e (.reg (.dup 2)) (ri_dup (by rfl))  -- e0d DUP3
  xs 0xe0f (.reg .mul) ri_mul  -- e0e MUL
  xs 0xe10 (.reg (.dup 2)) (ri_dup (by rfl))  -- e0f DUP3
  xs 0xe11 (.reg .iszero) ri_iszero  -- e10 ISZERO
  xs 0xe12 (.reg (.dup 2)) (ri_dup (by rfl))  -- e11 DUP3
  xs 0xe13 (.reg (.dup 4)) (ri_dup (by rfl))  -- e12 DUP5
  xs 0xe14 (.reg (.dup 3)) (ri_dup (by rfl))  -- e13 DUP4
  xs 0xe15 (.reg .div) ri_div  -- e14 DIV
  xs 0xe16 (.reg .eq) ri_eq  -- e15 EQ
  xs 0xe17 (.reg .or) ri_or  -- e16 OR
  xs 0xe1a (.push [0x0e, 0x1f] (by decide)) ri_push  -- e17 PUSH2 0x0e1f
  xji 0xe1b 0xe1f hw
  · xdead
  have hmul := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0xe20  -- e1f JUMPDEST
  xs 0xe21 (.reg (.dup 0)) (ri_dup (by rfl))  -- e20 DUP1
  xs 0xe22 (.reg (.swap 0)) (ri_swap (by rfl))  -- e21 SWAP1
  xs 0xe23 (.reg .pop) ri_pop  -- e22 POP
  xs 0xe24 (.reg (.swap 0)) (ri_swap (by rfl))  -- e23 SWAP1
  xs 0xe25 (.reg .pop) ri_pop  -- e24 POP
  xs 0xe26 (.reg (.swap 0)) (ri_swap (by rfl))  -- e25 SWAP1
  xs 0xe27 (.reg .pop) ri_pop  -- e26 POP
  xs 0xe2a (.push [0x02, 0x00] (by decide)) ri_push  -- e27 PUSH2 0x0200
  xl 0xe2b 0x200  -- e2a MLOAD
  xs 0xe2c (.reg (.dup 0)) (ri_dup (by rfl))  -- e2b DUP1
  xs 0xe2d (.reg (.dup 0)) (ri_dup (by rfl))  -- e2c DUP1
  xs 0xe30 (.push [0x0e, 0x35] (by decide)) ri_push  -- e2d PUSH2 0x0e35
  xji 0xe31 0xe35 hw
  · xdead
  have hD0 := hw
  clear hw
  xjd 0xe36  -- e35 JUMPDEST
  xs 0xe37 (.reg (.dup 2)) (ri_dup (by rfl))  -- e36 DUP3
  xs 0xe38 (.reg .div) ri_div  -- e37 DIV
  xs 0xe39 (.reg (.swap 0)) (ri_swap (by rfl))  -- e38 SWAP1
  xs 0xe3a (.reg .pop) ri_pop  -- e39 POP
  xs 0xe3b (.reg (.swap 0)) (ri_swap (by rfl))  -- e3a SWAP1
  xs 0xe3c (.reg .pop) ri_pop  -- e3b POP
  xs 0xe3e (.push [0x00] (by decide)) ri_push  -- e3c PUSH1 0x00
  have hfinalwf := hV.wf
  xsw 0xe3f 0x0  -- e3e MSTORE
  xs 0xe41 (.push [0x20] (by decide)) ri_push  -- e3f PUSH1 0x20
  xs 0xe43 (.push [0x00] (by decide)) ri_push  -- e41 PUSH1 0x00
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨rfl, hmul, hD0, fun a => by rw [hstor], by rw [hlogs], ?_⟩
  rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl, Mem.read_write_word_of_wf hfinalwf]

-- SEGMENT: ctaTail
/-- **From `D1` at `0x340` (`0xd77`) to the `RETURN`**: `totalSupply()` from the token (the
frame's only child, static, a word back), the checked difference by the deposit flag, and the
output `diff · supply / D0`. -/
theorem xa_cta_tail {M : Mem} {D0 D1 : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hV : VW M [(0x340, D1), (0x200, D0)])
    (h : XAt sevm post 0xd77 (St b [] M G) L) :
    ∃ c df, L = [c] ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      ((ctaDep sevm ≠ 0 ∧ D0.toNat ≤ D1.toNat ∧ df = D1 - D0) ∨
        (ctaDep sevm = 0 ∧ D1.toNat ≤ D0.toNat ∧ df = D0 - D1)) ∧
      B256.Nofm df (vSupply c) ∧ D0 ≠ 0 ∧ (∀ a, post.getStor a = b.getStor a) ∧
      post.logs = b.logs ∧ post.output = (df * vSupply c / D0).toBytes := by
  xs 0xd79 (.push [0x20] (by decide)) ri_push  -- d77 PUSH1 0x20
  xs 0xd7c (.push [0x04, 0xe0] (by decide)) ri_push  -- d79 PUSH2 0x04e0
  xs 0xd7e (.push [0x04] (by decide)) ri_push  -- d7c PUSH1 0x04
  xs 0xd83 (.push [0x18, 0x16, 0x0d, 0xdd] (by decide)) ri_push  -- d7e PUSH4 0x18160ddd
  xs 0xd86 (.push [0x04, 0x80] (by decide)) ri_push  -- d83 PUSH2 0x0480
  have hW0 := hV.wf
  xsw 0xd87 0x480  -- d86 MSTORE
  xs 0xd8a (.push [0x04, 0x9c] (by decide)) ri_push  -- d87 PUSH2 0x049c
  xs 0xd8c (.push [0x05] (by decide)) ri_push  -- d8a PUSH1 0x05
  xw 0xd8d (.reg .sload) ri_sload  -- d8c SLOAD
  xs 0xd8e (.reg .gas) ri_gas_remaining  -- d8d GAS
  obtain ⟨d, flag, out, M', L1, h, hVo, hrd, hob, hstor, hlogs, hk⟩ :=
    xa_staticcallV (pc' := 0xd8f) (o := 0x4e0) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl hV h
  clear hV
  xs 0xd92 (.push [0x0d, 0x97] (by decide)) ri_push  -- d8f PUSH2 0x0d97
  xji 0xd93 0xd97 hw
  · xdead
  xjd 0xd98  -- d97 JUMPDEST
  xs 0xd9a (.push [0x1f] (by decide)) ri_push  -- d98 PUSH1 0x1f
  xs 0xd9b (.reg .returndatasize) ri_returndatasize  -- d9a RETURNDATASIZE
  xs 0xd9c (.reg .gt) ri_gt  -- d9b GT
  xs 0xd9f (.push [0x0d, 0xa4] (by decide)) ri_push  -- d9c PUSH2 0x0da4
  have hwf := hw
  clear hw
  rcases hk hwf with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre (by rw [getStorVal_eq, tokenSlot_lit]; exact htok)
  clear hk
  subst hcout
  xji 0xda0 0xda4 hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have e := gtCheck_ne_zero hw
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw
  have hV := hVo hlen
  clear hVo
  vnorm
  xjd 0xda5  -- da4 JUMPDEST
  xs 0xda7 (.push [0x00] (by decide)) ri_push  -- da5 PUSH1 0x00
  xs 0xda8 (.reg .pop) ri_pop  -- da7 POP
  xs 0xdab (.push [0x04, 0xe0] (by decide)) ri_push  -- da8 PUSH2 0x04e0
  xl 0xdac 0x4e0  -- dab MLOAD
  xs 0xdaf (.push [0x04, 0x60] (by decide)) ri_push  -- dac PUSH2 0x0460
  xsw 0xdb0 0x460  -- daf MSTORE
  xs 0xdb2 (.push [0x00] (by decide)) ri_push  -- db0 PUSH1 0x00
  xs 0xdb5 (.push [0x05, 0x00] (by decide)) ri_push  -- db2 PUSH2 0x0500
  xsw 0xdb6 0x500  -- db5 MSTORE
  xs 0xdb8 (.push [0x64] (by decide)) ri_push  -- db6 PUSH1 0x64
  xs 0xdb9 (.reg .calldataload) ri_calldataload  -- db8 CALLDATALOAD
  xs 0xdba (.reg .iszero) ri_iszero  -- db9 ISZERO
  xs 0xdbd (.push [0x0d, 0xe2] (by decide)) ri_push  -- dba PUSH2 0x0de2
  xji 0xdbe 0xde2 hw
  swap
  · have hd0 := eqCheck_ne_zero_eq hw
    clear hw
    xjd 0xde3  -- de2 JUMPDEST
    xs 0xde6 (.push [0x02, 0x00] (by decide)) ri_push  -- de3 PUSH2 0x0200
    xl 0xde7 0x200  -- de6 MLOAD
    xs 0xdea (.push [0x03, 0x40] (by decide)) ri_push  -- de7 PUSH2 0x0340
    xl 0xdeb 0x340  -- dea MLOAD
    xs 0xdec (.reg (.dup 0)) (ri_dup (by rfl))  -- deb DUP1
    xs 0xded (.reg (.dup 2)) (ri_dup (by rfl))  -- dec DUP3
    xs 0xdee (.reg .lt) ri_lt  -- ded LT
    xs 0xdef (.reg .iszero) ri_iszero  -- dee ISZERO
    xs 0xdf2 (.push [0x0d, 0xf7] (by decide)) ri_push  -- def PUSH2 0x0df7
    xji 0xdf3 0xdf7 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0xdf8  -- df7 JUMPDEST
    xs 0xdf9 (.reg (.dup 0)) (ri_dup (by rfl))  -- df8 DUP1
    xs 0xdfa (.reg (.dup 2)) (ri_dup (by rfl))  -- df9 DUP3
    xs 0xdfb (.reg .sub) ri_sub  -- dfa SUB
    xs 0xdfc (.reg (.swap 0)) (ri_swap (by rfl))  -- dfb SWAP1
    xs 0xdfd (.reg .pop) ri_pop  -- dfc POP
    xs 0xdfe (.reg (.swap 0)) (ri_swap (by rfl))  -- dfd SWAP1
    xs 0xdff (.reg .pop) ri_pop  -- dfe POP
    xs 0xe02 (.push [0x05, 0x00] (by decide)) ri_push  -- dff PUSH2 0x0500
    xsw 0xe03 0x500  -- e02 MSTORE
    obtain ⟨hL1, hm, hD0, hs, hl, ho⟩ := xa_cta_fin (df := D0 - D1) (T := vSupply c) (D0 := D0)
      hcode (hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])) h
    refine ⟨c, _, by rw [hL, hL1], ⟨?_, ?_, hstat, hlen, hclogs⟩, .inr ⟨hd0, hle, rfl⟩, hm, hD0,
      fun a => by rw [hs, hstor, afterSload_getStor], by rw [hl, hlogs, afterSload_logs], ho⟩
    · rw [htgt, getStorVal_eq, tokenSlot_lit]
    · rw [hdata, show (Bytes.toB256 [4, 0x9c]).toNat = 1180 from rfl,
        show (Bytes.toB256 [4]).toNat = 4 from rfl,
        Mem.read_write_word_inside hW0 1152 _ (by decide) (by decide)]
      decide
  have hd1 := eqCheck_eq_zero hw
  clear hw
  xs 0xdc1 (.push [0x03, 0x40] (by decide)) ri_push  -- dbe PUSH2 0x0340
  xl 0xdc2 0x340  -- dc1 MLOAD
  xs 0xdc5 (.push [0x02, 0x00] (by decide)) ri_push  -- dc2 PUSH2 0x0200
  xl 0xdc6 0x200  -- dc5 MLOAD
  xs 0xdc7 (.reg (.dup 0)) (ri_dup (by rfl))  -- dc6 DUP1
  xs 0xdc8 (.reg (.dup 2)) (ri_dup (by rfl))  -- dc7 DUP3
  xs 0xdc9 (.reg .lt) ri_lt  -- dc8 LT
  xs 0xdca (.reg .iszero) ri_iszero  -- dc9 ISZERO
  xs 0xdcd (.push [0x0d, 0xd2] (by decide)) ri_push  -- dca PUSH2 0x0dd2
  xji 0xdce 0xdd2 hw
  · xdead
  have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0xdd3  -- dd2 JUMPDEST
  xs 0xdd4 (.reg (.dup 0)) (ri_dup (by rfl))  -- dd3 DUP1
  xs 0xdd5 (.reg (.dup 2)) (ri_dup (by rfl))  -- dd4 DUP3
  xs 0xdd6 (.reg .sub) ri_sub  -- dd5 SUB
  xs 0xdd7 (.reg (.swap 0)) (ri_swap (by rfl))  -- dd6 SWAP1
  xs 0xdd8 (.reg .pop) ri_pop  -- dd7 POP
  xs 0xdd9 (.reg (.swap 0)) (ri_swap (by rfl))  -- dd8 SWAP1
  xs 0xdda (.reg .pop) ri_pop  -- dd9 POP
  xs 0xddd (.push [0x05, 0x00] (by decide)) ri_push  -- dda PUSH2 0x0500
  xsw 0xdde 0x500  -- ddd MSTORE
  xs 0xde1 (.push [0x0e, 0x03] (by decide)) ri_push  -- dde PUSH2 0x0e03
  xjmp 0xe03  -- de1 JUMP
  obtain ⟨hL1, hm, hD0, hs, hl, ho⟩ := xa_cta_fin (df := D1 - D0) (T := vSupply c) (D0 := D0)
    hcode (hV.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])) h
  refine ⟨c, _, by rw [hL, hL1], ⟨?_, ?_, hstat, hlen, hclogs⟩, .inl ⟨hd1, hle, rfl⟩, hm, hD0,
    fun a => by rw [hs, hstor, afterSload_getStor], by rw [hl, hlogs, afterSload_logs], ho⟩
  · rw [htgt, getStorVal_eq, tokenSlot_lit]
  · rw [hdata, show (Bytes.toB256 [4, 0x9c]).toNat = 1180 from rfl,
      show (Bytes.toB256 [4]).toNat = 4 from rfl,
      Mem.read_write_word_inside hW0 1152 _ (by decide) (by decide)]
    decide

end

end Blanc.Lift.Curve3Pool
