import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceDispatch
import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXSpec
import Blanc.Lift.Curve3Pool.Walk.Exchange

/-!
# `remove_liquidity_imbalance` on the word carrier, part 1: guards, supply, `_A`, balances

`xa_rli_front` (`0x304f` → the first frame save's head `0x31b7`): `assert lock == 0; lock = 1`,
the non-payable guard, `assert not is_killed`, `token.totalSupply()` (the frame's next child,
static, at least a word back) with `total_supply != 0`, `_fee = fee * 3 / 8` and `admin_fee`,
the eight words `0x140 … 0x220` pushed around `_A` (crossed with `xa_vAV`) and written back,
`amp` at `0x220`, `old_balances` loaded from storage to `0x280` and copied to `new_balances` at
`0x2e0`. The walk runs over the views' word carrier `VW` (the dispatcher's memory is aligned),
with no premise on the token beyond its not being a precompile: the base's code at address 4 is
carried through the child by the caller's per-child premise.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: rliFront
/-- **Guards, supply, `_A` and the balances** (`0x304f` → `0x31b7`). -/
theorem xa_rli_front (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x304f (St b [] (vdMem sevm) G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (A : B256) (b' : Devm) (M' : Mem) (G' : Nat),
      L = c :: L' ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      vSupply c ≠ 0 ∧ ((b.getStor sevm.currentTarget).get feeSlot).Nofm (Bytes.toB256 [3]) ∧
      aChk s sevm.benvStat.time.toNat = some A.toNat ∧
      (∀ x, (b'.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) ∧
      b'.logs = b.logs ∧ b'.output = b.output ∧
      (∀ x, b.getCode x ≠ .empty → b'.getCode x = b.getCode x) ∧
      (IdReady sevm b → c.post.getCode 4 = c.pre.getCode 4 → IdReady sevm b') ∧
      XAt sevm post 0x31b7 (St b' [] M' G') L' ∧
      VW M' [(0x360, Bytes.toB256 [1, 64]), (0x140, vSupply c),
        (0x1e0, (b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]),
        (0x200, (b.getStor sevm.currentTarget).get adminFeeSlot), (0x220, A),
        (0x280, balAt (b.getStor sevm.currentTarget) 0),
        (0x2a0, balAt (b.getStor sevm.currentTarget) 1),
        (0x2c0, balAt (b.getStor sevm.currentTarget) 2),
        (0x2e0, balAt (b.getStor sevm.currentTarget) 0),
        (0x300, balAt (b.getStor sevm.currentTarget) 1),
        (0x320, balAt (b.getStor sevm.currentTarget) 2)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x3053 (.push [0xff, 0xff, 0xff] (by decide)) ri_push  -- 304f PUSH3 0xffffff
  xw 0x3054 (.reg .sload) ri_sload  -- 3053 SLOAD
  xs 0x3055 (.reg .iszero) ri_iszero  -- 3054 ISZERO
  xs 0x3058 (.push [0x30, 0x5d] (by decide)) ri_push  -- 3055 PUSH2 0x305d
  xji 0x3059 0x305d hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xjd 0x305e  -- 305d JUMPDEST
  xs 0x3060 (.push [0x01] (by decide)) ri_push  -- 305e PUSH1 0x01
  xs 0x3064 (.push [0xff, 0xff, 0xff] (by decide)) ri_push  -- 3060 PUSH3 0xffffff
  xw 0x3065 (.reg .sstore) ri_sstore  -- 3064 SSTORE
  xs 0x3066 (.reg .callvalue) ri_callvalue  -- 3065 CALLVALUE
  xs 0x3067 (.reg .iszero) ri_iszero  -- 3066 ISZERO
  xs 0x306a (.push [0x30, 0x6f] (by decide)) ri_push  -- 3067 PUSH2 0x306f
  xji 0x306b 0x306f hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x3070  -- 306f JUMPDEST
  xs 0x3072 (.push [0x0f] (by decide)) ri_push  -- 3070 PUSH1 0x0f
  xw 0x3073 (.reg .sload) ri_sload  -- 3072 SLOAD
  xs 0x3074 (.reg .iszero) ri_iszero  -- 3073 ISZERO
  xs 0x3077 (.push [0x30, 0x7c] (by decide)) ri_push  -- 3074 PUSH2 0x307c
  xji 0x3078 0x307c hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [isKilledSlot_lit, getStorVal_afterSstore_ne (by decide), getStorVal_afterSload,
      getStorVal_eq] at e
    exact e
  clear hw
  xjd 0x307d  -- 307c JUMPDEST
  xs 0x307f (.push [0x20] (by decide)) ri_push  -- 307d PUSH1 0x20
  xs 0x3082 (.push [0x01, 0xc0] (by decide)) ri_push  -- 307f PUSH2 0x01c0
  xs 0x3084 (.push [0x04] (by decide)) ri_push  -- 3082 PUSH1 0x04
  xs 0x3089 (.push [0x18, 0x16, 0x0d, 0xdd] (by decide)) ri_push  -- 3084 PUSH4 0x18160ddd
  xs 0x308c (.push [0x01, 0x60] (by decide)) ri_push  -- 3089 PUSH2 0x0160
  xsw 0x308d 0x160  -- 308c MSTORE
  xs 0x3090 (.push [0x01, 0x7c] (by decide)) ri_push  -- 308d PUSH2 0x017c
  xs 0x3092 (.push [0x05] (by decide)) ri_push  -- 3090 PUSH1 0x05
  xw 0x3093 (.reg .sload) ri_sload  -- 3092 SLOAD
  xs 0x3094 (.reg .gas) ri_gas_remaining  -- 3093 GAS
  obtain ⟨d, flag, out, M', L1, h, hVo, hrd, hob, hstor, hlogs, hk⟩ :=
    xa_staticcallV (pc' := 0x3095) (o := 0x1c0) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl hV h
  clear hV
  xs 0x3098 (.push [0x30, 0x9d] (by decide)) ri_push  -- 3095 PUSH2 0x309d
  xji 0x3099 0x309d hw
  · xdead
  have hwf := hw
  clear hw
  rcases hk hwf with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre (by
      rw [getStorVal_eq, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor,
        tokenSlot_lit, Stor.get_set_ne _ (show Bytes.toB256 [255, 255, 255] ≠ tokenSlot by decide)]
      exact htok)
  clear hk hwf
  subst hcout
  xjd 0x309e  -- 309d JUMPDEST
  xs 0x30a0 (.push [0x1f] (by decide)) ri_push  -- 309e PUSH1 0x1f
  xs 0x30a1 (.reg .returndatasize) ri_returndatasize  -- 30a0 RETURNDATASIZE
  xs 0x30a2 (.reg .gt) ri_gt  -- 30a1 GT
  xs 0x30a5 (.push [0x30, 0xaa] (by decide)) ri_push  -- 30a2 PUSH2 0x30aa
  xji 0x30a6 0x30aa hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have e := gtCheck_ne_zero hw
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw
  have hV := hVo hlen
  clear hVo
  vnorm
  xjd 0x30ab  -- 30aa JUMPDEST
  xs 0x30ad (.push [0x00] (by decide)) ri_push  -- 30ab PUSH1 0x00
  xs 0x30ae (.reg .pop) ri_pop  -- 30ad POP
  xs 0x30b1 (.push [0x01, 0xc0] (by decide)) ri_push  -- 30ae PUSH2 0x01c0
  xl 0x30b2 0x1c0  -- 30b1 MLOAD
  xs 0x30b5 (.push [0x01, 0x40] (by decide)) ri_push  -- 30b2 PUSH2 0x0140
  xsw 0x30b6 0x140  -- 30b5 MSTORE
  xs 0x30b8 (.push [0x00] (by decide)) ri_push  -- 30b6 PUSH1 0x00
  xs 0x30bb (.push [0x01, 0x40] (by decide)) ri_push  -- 30b8 PUSH2 0x0140
  xl 0x30bc 0x140  -- 30bb MLOAD
  xs 0x30bd (.reg .xor) ri_xor  -- 30bc XOR
  xs 0x30c0 (.push [0x30, 0xc5] (by decide)) ri_push  -- 30bd PUSH2 0x30c5
  xji 0x30c1 0x30c5 hw
  · xdead
  have hT0 : vSupply c ≠ 0 := by
    rw [zero_lit, B256.xor_zero] at hw
    exact hw
  clear hw
  xjd 0x30c6  -- 30c5 JUMPDEST
  xs 0x30c8 (.push [0x02] (by decide)) ri_push  -- 30c6 PUSH1 0x02
  xw 0x30c9 (.reg .sload) ri_sload  -- 30c8 SLOAD
  xs 0x30cb (.push [0x03] (by decide)) ri_push  -- 30c9 PUSH1 0x03
  xs 0x30cc (.reg (.dup 0)) (ri_dup (by rfl))  -- 30cb DUP1
  xs 0x30cd (.reg (.dup 2)) (ri_dup (by rfl))  -- 30cc DUP3
  xs 0x30ce (.reg .mul) ri_mul  -- 30cd MUL
  xs 0x30cf (.reg (.dup 2)) (ri_dup (by rfl))  -- 30ce DUP3
  xs 0x30d0 (.reg .iszero) ri_iszero  -- 30cf ISZERO
  xs 0x30d1 (.reg (.dup 2)) (ri_dup (by rfl))  -- 30d0 DUP3
  xs 0x30d2 (.reg (.dup 4)) (ri_dup (by rfl))  -- 30d1 DUP5
  xs 0x30d3 (.reg (.dup 3)) (ri_dup (by rfl))  -- 30d2 DUP4
  xs 0x30d4 (.reg .div) ri_div  -- 30d3 DIV
  xs 0x30d5 (.reg .eq) ri_eq  -- 30d4 EQ
  xs 0x30d6 (.reg .or) ri_or  -- 30d5 OR
  xs 0x30d9 (.push [0x30, 0xde] (by decide)) ri_push  -- 30d6 PUSH2 0x30de
  xji 0x30da 0x30de hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x30df  -- 30de JUMPDEST
  xs 0x30e0 (.reg (.dup 0)) (ri_dup (by rfl))  -- 30df DUP1
  xs 0x30e1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 30e0 SWAP1
  xs 0x30e2 (.reg .pop) ri_pop  -- 30e1 POP
  xs 0x30e3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 30e2 SWAP1
  xs 0x30e4 (.reg .pop) ri_pop  -- 30e3 POP
  xs 0x30e5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 30e4 SWAP1
  xs 0x30e6 (.reg .pop) ri_pop  -- 30e5 POP
  xs 0x30e8 (.push [0x08] (by decide)) ri_push  -- 30e6 PUSH1 0x08
  xs 0x30e9 (.reg (.dup 0)) (ri_dup (by rfl))  -- 30e8 DUP1
  xs 0x30ea (.reg (.dup 0)) (ri_dup (by rfl))  -- 30e9 DUP1
  xs 0x30ed (.push [0x30, 0xf2] (by decide)) ri_push  -- 30ea PUSH2 0x30f2
  xji 0x30ee 0x30f2 hw
  · xdead
  clear hw
  xjd 0x30f3  -- 30f2 JUMPDEST
  xs 0x30f4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 30f3 DUP3
  xs 0x30f5 (.reg .div) ri_div  -- 30f4 DIV
  xs 0x30f6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 30f5 SWAP1
  xs 0x30f7 (.reg .pop) ri_pop  -- 30f6 POP
  xs 0x30f8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 30f7 SWAP1
  xs 0x30f9 (.reg .pop) ri_pop  -- 30f8 POP
  xs 0x30fc (.push [0x01, 0xe0] (by decide)) ri_push  -- 30f9 PUSH2 0x01e0
  xsw 0x30fd 0x1e0  -- 30fc MSTORE
  xs 0x30ff (.push [0x03] (by decide)) ri_push  -- 30fd PUSH1 0x03
  xw 0x3100 (.reg .sload) ri_sload  -- 30ff SLOAD
  xs 0x3103 (.push [0x02, 0x00] (by decide)) ri_push  -- 3100 PUSH2 0x0200
  xsw 0x3104 0x200  -- 3103 MSTORE
  xs 0x3107 (.push [0x01, 0x40] (by decide)) ri_push  -- 3104 PUSH2 0x0140
  xl 0x3108 0x140  -- 3107 MLOAD
  xs 0x310b (.push [0x01, 0x60] (by decide)) ri_push  -- 3108 PUSH2 0x0160
  xl 0x310c 0x160  -- 310b MLOAD
  xs 0x310f (.push [0x01, 0x80] (by decide)) ri_push  -- 310c PUSH2 0x0180
  xlu 0x3110  -- 310f MLOAD
  xs 0x3113 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3110 PUSH2 0x01a0
  xlu 0x3114  -- 3113 MLOAD
  xs 0x3117 (.push [0x01, 0xc0] (by decide)) ri_push  -- 3114 PUSH2 0x01c0
  xl 0x3118 0x1c0  -- 3117 MLOAD
  xs 0x311b (.push [0x01, 0xe0] (by decide)) ri_push  -- 3118 PUSH2 0x01e0
  xl 0x311c 0x1e0  -- 311b MLOAD
  xs 0x311f (.push [0x02, 0x00] (by decide)) ri_push  -- 311c PUSH2 0x0200
  xl 0x3120 0x200  -- 311f MLOAD
  xs 0x3123 (.push [0x02, 0x20] (by decide)) ri_push  -- 3120 PUSH2 0x0220
  xlu 0x3124  -- 3123 MLOAD
  xs 0x3126 (.push [0x06] (by decide)) ri_push  -- 3124 PUSH1 0x06
  cvpc 0x3127  -- 3126 PC
  xs 0x3128 (.reg .add) ri_add  -- 3127 ADD
  xs 0x312b (.push [0x00, 0xa9] (by decide)) ri_push  -- 3128 PUSH2 0x00a9
  xjmp 0xa9  -- 312b JUMP
  have hs1 : ∀ x, ((afterSload sevm (afterSload sevm d (Bytes.toB256 [2])) (Bytes.toB256 [3])).getStor
      sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [afterSload_getStor, afterSload_getStor, hstor, afterSload_getStor, afterSload_getStor,
      afterSstore_getStor_self, afterSload_getStor, lockSlot_lit,
      show Bytes.toB256 [1] = (1 : B256) from by decide]
  have ha1 := ha.of_lock fun x hx => by rw [hs1, Stor.get_set_ne _ (Ne.symm hx)]
  obtain ⟨A, b2, M2, _, hb2, h, hA, hV1⟩ := xa_vAV hc hcode hfork ha1 hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  rw [show (Nat.toB256 12582 + Bytes.toB256 [6]).toNat = 0x312c from by decide] at h
  xjd 0x312d  -- 312c JUMPDEST
  xs 0x3130 (.push [0x02, 0x60] (by decide)) ri_push  -- 312d PUSH2 0x0260
  xsw 0x3131 0x260  -- 3130 MSTORE
  xs 0x3134 (.push [0x02, 0x20] (by decide)) ri_push  -- 3131 PUSH2 0x0220
  xsw 0x3135 0x220  -- 3134 MSTORE
  xs 0x3138 (.push [0x02, 0x00] (by decide)) ri_push  -- 3135 PUSH2 0x0200
  xsw 0x3139 0x200  -- 3138 MSTORE
  xs 0x313c (.push [0x01, 0xe0] (by decide)) ri_push  -- 3139 PUSH2 0x01e0
  xsw 0x313d 0x1e0  -- 313c MSTORE
  xs 0x3140 (.push [0x01, 0xc0] (by decide)) ri_push  -- 313d PUSH2 0x01c0
  xsw 0x3141 0x1c0  -- 3140 MSTORE
  xs 0x3144 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3141 PUSH2 0x01a0
  xsw 0x3145 0x1a0  -- 3144 MSTORE
  xs 0x3148 (.push [0x01, 0x80] (by decide)) ri_push  -- 3145 PUSH2 0x0180
  xsw 0x3149 0x180  -- 3148 MSTORE
  xs 0x314c (.push [0x01, 0x60] (by decide)) ri_push  -- 3149 PUSH2 0x0160
  xsw 0x314d 0x160  -- 314c MSTORE
  xs 0x3150 (.push [0x01, 0x40] (by decide)) ri_push  -- 314d PUSH2 0x0140
  xsw 0x3151 0x140  -- 3150 MSTORE
  xs 0x3154 (.push [0x02, 0x60] (by decide)) ri_push  -- 3151 PUSH2 0x0260
  xl 0x3155 0x260  -- 3154 MLOAD
  xs 0x3158 (.push [0x02, 0x20] (by decide)) ri_push  -- 3155 PUSH2 0x0220
  xsw 0x3159 0x220  -- 3158 MSTORE
  xs 0x315c (.push [0x02, 0x80] (by decide)) ri_push  -- 3159 PUSH2 0x0280
  xs 0x315e (.push [0x01] (by decide)) ri_push  -- 315c PUSH1 0x01
  xs 0x315f (.reg (.dup 0)) (ri_dup (by rfl))  -- 315e DUP1
  xs 0x3161 (.push [0xc0] (by decide)) ri_push  -- 315f PUSH1 0xc0
  xsw 0x3162 0xc0  -- 3161 MSTORE
  xs 0x3164 (.push [0x20] (by decide)) ri_push  -- 3162 PUSH1 0x20
  xs 0x3166 (.push [0xc0] (by decide)) ri_push  -- 3164 PUSH1 0xc0
  xk 0x3167 0xc0  -- 3166 SHA3
  xw 0x3168 (.reg .sload) ri_sload  -- 3167 SLOAD
  xs 0x3169 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3168 DUP3
  xsw 0x316a 0x280  -- 3169 MSTORE
  xs 0x316c (.push [0x01] (by decide)) ri_push  -- 316a PUSH1 0x01
  xs 0x316d (.reg (.dup 1)) (ri_dup (by rfl))  -- 316c DUP2
  xs 0x316f (.push [0xc0] (by decide)) ri_push  -- 316d PUSH1 0xc0
  xsw 0x3170 0xc0  -- 316f MSTORE
  xs 0x3172 (.push [0x20] (by decide)) ri_push  -- 3170 PUSH1 0x20
  xs 0x3174 (.push [0xc0] (by decide)) ri_push  -- 3172 PUSH1 0xc0
  xk 0x3175 0xc0  -- 3174 SHA3
  xs 0x3176 (.reg .add) ri_add  -- 3175 ADD
  xw 0x3177 (.reg .sload) ri_sload  -- 3176 SLOAD
  xs 0x3178 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3177 DUP3
  xs 0x317a (.push [0x20] (by decide)) ri_push  -- 3178 PUSH1 0x20
  xs 0x317b (.reg .add) ri_add  -- 317a ADD
  xsw 0x317c 0x2a0  -- 317b MSTORE
  xs 0x317e (.push [0x02] (by decide)) ri_push  -- 317c PUSH1 0x02
  xs 0x317f (.reg (.dup 1)) (ri_dup (by rfl))  -- 317e DUP2
  xs 0x3181 (.push [0xc0] (by decide)) ri_push  -- 317f PUSH1 0xc0
  xsw 0x3182 0xc0  -- 3181 MSTORE
  xs 0x3184 (.push [0x20] (by decide)) ri_push  -- 3182 PUSH1 0x20
  xs 0x3186 (.push [0xc0] (by decide)) ri_push  -- 3184 PUSH1 0xc0
  xk 0x3187 0xc0  -- 3186 SHA3
  xs 0x3188 (.reg .add) ri_add  -- 3187 ADD
  xw 0x3189 (.reg .sload) ri_sload  -- 3188 SLOAD
  xs 0x318a (.reg (.dup 2)) (ri_dup (by rfl))  -- 3189 DUP3
  xs 0x318c (.push [0x40] (by decide)) ri_push  -- 318a PUSH1 0x40
  xs 0x318d (.reg .add) ri_add  -- 318c ADD
  xsw 0x318e 0x2c0  -- 318d MSTORE
  xs 0x318f (.reg .pop) ri_pop  -- 318e POP
  xs 0x3190 (.reg .pop) ri_pop  -- 318f POP
  xs 0x3193 (.push [0x02, 0xe0] (by decide)) ri_push  -- 3190 PUSH2 0x02e0
  xs 0x3196 (.push [0x02, 0x80] (by decide)) ri_push  -- 3193 PUSH2 0x0280
  xs 0x3197 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3196 DUP1
  xl 0x3198 0x280  -- 3197 MLOAD
  xs 0x3199 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3198 DUP3
  xsw 0x319a 0x2e0  -- 3199 MSTORE
  xs 0x319b (.reg (.dup 0)) (ri_dup (by rfl))  -- 319a DUP1
  xs 0x319d (.push [0x20] (by decide)) ri_push  -- 319b PUSH1 0x20
  xs 0x319e (.reg .add) ri_add  -- 319d ADD
  xl 0x319f 0x2a0  -- 319e MLOAD
  xs 0x31a0 (.reg (.dup 2)) (ri_dup (by rfl))  -- 319f DUP3
  xs 0x31a2 (.push [0x20] (by decide)) ri_push  -- 31a0 PUSH1 0x20
  xs 0x31a3 (.reg .add) ri_add  -- 31a2 ADD
  xsw 0x31a4 0x300  -- 31a3 MSTORE
  xs 0x31a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 31a4 DUP1
  xs 0x31a7 (.push [0x40] (by decide)) ri_push  -- 31a5 PUSH1 0x40
  xs 0x31a8 (.reg .add) ri_add  -- 31a7 ADD
  xl 0x31a9 0x2c0  -- 31a8 MLOAD
  xs 0x31aa (.reg (.dup 2)) (ri_dup (by rfl))  -- 31a9 DUP3
  xs 0x31ac (.push [0x40] (by decide)) ri_push  -- 31aa PUSH1 0x40
  xs 0x31ad (.reg .add) ri_add  -- 31ac ADD
  xsw 0x31ae 0x320  -- 31ad MSTORE
  xs 0x31af (.reg .pop) ri_pop  -- 31ae POP
  xs 0x31b0 (.reg .pop) ri_pop  -- 31af POP
  xs 0x31b3 (.push [0x01, 0x40] (by decide)) ri_push  -- 31b0 PUSH2 0x0140
  xs 0x31b6 (.push [0x03, 0x60] (by decide)) ri_push  -- 31b3 PUSH2 0x0360
  xsw 0x31b7 0x360  -- 31b6 MSTORE
  have hd : ∀ x, (d.getStor sevm.currentTarget).get x =
      ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [← hs1, afterSload_getStor, afterSload_getStor]
  have hB2 : ∀ x, (b2.getStor sevm.currentTarget).get x =
      ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [hb2.getStor, hs1]
  simp (config := {decide := true}) only [show Bytes.toB256 [1] = (1 : B256) from by decide,
    balancesBase_eq, getStorVal_eq, afterSload_getStor, hB2, hd, Stor.get_set_ite, ↓reduceIte]
    at h hV hm3
  rw [← feeSlot_lit, ← adminFeeSlot_lit]
  rw [show balancesBase = balancesBase + Nat.toB256 0 from by decide,
    show balancesBase + Nat.toB256 0 + 1 = balancesBase + Nat.toB256 1 from by decide,
    show balancesBase + Nat.toB256 0 + Bytes.toB256 [2] = balancesBase + Nat.toB256 2 from by decide]
    at hV
  have hB0 : IdReady sevm b → IdReady sevm (afterSload sevm (afterSload sevm (afterSstore sevm
      (afterSload sevm b (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255])
      (Bytes.toB256 [1])) (Bytes.toB256 [15])) (Bytes.toB256 [5])) := fun hb =>
    (((hb.afterSload _).afterSstore _ _).afterSload _).afterSload _
  refine ⟨hlock, hval, hkill, c, L1, A, _, _, _, hL, ⟨?_, ?_, hstat, hlen, hclogs⟩, hT0, hm3, hA,
    fun x => ?_, ?_, ?_, fun x hx => ?_, fun hb h4 => ?_, h, hV.sub ?_⟩
  · rw [htgt, getStorVal_eq, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor,
      tokenSlot_lit, Stor.get_set_ne _ (show Bytes.toB256 [255, 255, 255] ≠ tokenSlot by decide)]
  · rw [hdata, show (Bytes.toB256 [1, 124]).toNat = 380 from rfl,
      show (Bytes.toB256 [4]).toNat = 4 from rfl,
      Mem.read_write_word_inside (vyMem_wf Mem.wf_empty _) 352 _ (by decide) (by decide)]
    decide
  · rw [afterSload_getStor, afterSload_getStor, afterSload_getStor, hB2]
  · rw [afterSload_logs, afterSload_logs, afterSload_logs, hb2.logs, afterSload_logs,
      afterSload_logs, hlogs, afterSload_logs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [afterSload_output, afterSload_output, afterSload_output, hb2.output, afterSload_output,
      afterSload_output, hout, afterSload_output, afterSload_output, afterSstore_output,
      afterSload_output]
  · rw [afterSload_getCode, afterSload_getCode, afterSload_getCode, cw_sloads_getCode hb2,
      afterSload_getCode, afterSload_getCode, hcodeK x (by
        rwa [afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode]),
      afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode]
  · have hb0 := hB0 hb
    have hdI : IdReady sevm d :=
      ⟨by rw [hcpost, h4, hcpre]; exact hb0.nodeleg, hacc _ hb0.warm, hb.pre, hb.fork⟩
    exact ((cw_sloads_idReady hb2 ((hdI.afterSload _).afterSload _)).afterSload _).afterSload _
      |>.afterSload _
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
