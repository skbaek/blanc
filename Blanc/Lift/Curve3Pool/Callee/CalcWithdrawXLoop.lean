import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXC

/-!
# `_calc_withdraw_one_coin`'s fee loop (`0x405e`), unrolled

Iteration `k` (counter at `0x720`): `scaled = xp[k] · D1 / D0` (checked), `dx_expected` by
whether `k = i` (`scaled - new_y`, else `xp[k] - scaled`, checked), and `xp_reduced[k] -=
fee · dx_expected / FEE_DENOMINATOR` (checked) at `0x540 + 32k`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- `FEE_DENOMINATOR` as pushed. -/
abbrev cwFeeDen : B256 := Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]

/-- One fee-loop step's checked arithmetic: `xp_reduced[k]` from `rk` to `r'`. -/
def CwStep (eqk : Prop) (xk D1 D0 y F rk r' : B256) : Prop :=
  B256.Nofm xk D1 ∧ D0 ≠ 0 ∧ ∃ dx : B256,
    ((eqk ∧ y.toNat ≤ (xk * D1 / D0).toNat ∧ dx = xk * D1 / D0 - y) ∨
      (¬ eqk ∧ (xk * D1 / D0).toNat ≤ xk.toNat ∧ dx = xk - xk * D1 / D0)) ∧
    B256.Nofm F dx ∧ (F * dx / cwFeeDen).toNat ≤ rk.toNat ∧ r' = rk - F * dx / cwFeeDen

section

variable {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {G : Nat}
  {L : List Exec.Frame}


/-- **Fee-loop iteration 0.** -/
theorem xa_cw_it0 {M : Mem} {a i A F T x0 x1 x2 D0 D1 y dy0 r0 r1 r2 ck : B256}
    (hcode : sevm.code = code) (hck : ck = Bytes.toB256 [0])
    (hV : VW M [(0x720, ck), (0x700, dy0), (0x5a0, y), (0x580, r2), (0x560, r1),
        (0x540, r0), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)])
    (h : XAt sevm post 0x405e
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G) L) :
    ∃ r' M' G', CwStep (Bytes.toB256 [0] = i) x0 D1 D0 y F r0 r' ∧
      XAt sevm post 0x405e
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' G') L ∧
      VW M' [(0x720, Bytes.toB256 [1] + Bytes.toB256 [0]), (0x700, dy0), (0x5a0, y), (0x580, r2), (0x560, r1),
        (0x540, r'), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)] := by
  subst hck
  xjd 0x405f  -- 405e JUMPDEST
  xs 0x4061 (.push [0x00] (by decide)) ri_push  -- 405f PUSH1 0x00
  xs 0x4064 (.push [0x07, 0x40] (by decide)) ri_push  -- 4061 PUSH2 0x0740
  xsw 0x4065 0x740  -- 4064 MSTORE
  xs 0x4068 (.push [0x01, 0x60] (by decide)) ri_push  -- 4065 PUSH2 0x0160
  xl 0x4069 0x160  -- 4068 MLOAD
  xs 0x406c (.push [0x07, 0x20] (by decide)) ri_push  -- 4069 PUSH2 0x0720
  xl 0x406d 0x720  -- 406c MLOAD
  xs 0x406e (.reg .eq) ri_eq  -- 406d EQ
  xs 0x406f (.reg .iszero) ri_iszero  -- 406e ISZERO
  xs 0x4072 (.push [0x40, 0xe0] (by decide)) ri_push  -- 406f PUSH2 0x40e0
  xji 0x4073 0x40e0 hw
  swap
  · have hne := eqCheck_eq_zero (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x40e1  -- 40e0 JUMPDEST
    xs 0x40e4 (.push [0x03, 0x20] (by decide)) ri_push  -- 40e1 PUSH2 0x0320
    xs 0x40e7 (.push [0x07, 0x20] (by decide)) ri_push  -- 40e4 PUSH2 0x0720
    xl 0x40e8 0x720  -- 40e7 MLOAD
    xs 0x40ea (.push [0x03] (by decide)) ri_push  -- 40e8 PUSH1 0x03
    xs 0x40eb (.reg (.dup 1)) (ri_dup (by rfl))  -- 40ea DUP2
    xs 0x40ec (.reg .lt) ri_lt  -- 40eb LT
    xs 0x40ef (.push [0x40, 0xf4] (by decide)) ri_push  -- 40ec PUSH2 0x40f4
    xji 0x40f0 0x40f4 hw
    · xdead
    clear hw
    xjd 0x40f5  -- 40f4 JUMPDEST
    xs 0x40f7 (.push [0x20] (by decide)) ri_push  -- 40f5 PUSH1 0x20
    xs 0x40f8 (.reg .mul) ri_mul  -- 40f7 MUL
    xs 0x40f9 (.reg .add) ri_add  -- 40f8 ADD
    xl 0x40fa 0x320  -- 40f9 MLOAD
    xs 0x40fd (.push [0x03, 0x20] (by decide)) ri_push  -- 40fa PUSH2 0x0320
    xs 0x4100 (.push [0x07, 0x20] (by decide)) ri_push  -- 40fd PUSH2 0x0720
    xl 0x4101 0x720  -- 4100 MLOAD
    xs 0x4103 (.push [0x03] (by decide)) ri_push  -- 4101 PUSH1 0x03
    xs 0x4104 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4103 DUP2
    xs 0x4105 (.reg .lt) ri_lt  -- 4104 LT
    xs 0x4108 (.push [0x41, 0x0d] (by decide)) ri_push  -- 4105 PUSH2 0x410d
    xji 0x4109 0x410d hw
    · xdead
    clear hw
    xjd 0x410e  -- 410d JUMPDEST
    xs 0x4110 (.push [0x20] (by decide)) ri_push  -- 410e PUSH1 0x20
    xs 0x4111 (.reg .mul) ri_mul  -- 4110 MUL
    xs 0x4112 (.reg .add) ri_add  -- 4111 ADD
    xl 0x4113 0x320  -- 4112 MLOAD
    xs 0x4116 (.push [0x05, 0x20] (by decide)) ri_push  -- 4113 PUSH2 0x0520
    xl 0x4117 0x520  -- 4116 MLOAD
    xs 0x4118 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4117 DUP1
    xs 0x4119 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4118 DUP3
    xs 0x411a (.reg .mul) ri_mul  -- 4119 MUL
    xs 0x411b (.reg (.dup 2)) (ri_dup (by rfl))  -- 411a DUP3
    xs 0x411c (.reg .iszero) ri_iszero  -- 411b ISZERO
    xs 0x411d (.reg (.dup 2)) (ri_dup (by rfl))  -- 411c DUP3
    xs 0x411e (.reg (.dup 4)) (ri_dup (by rfl))  -- 411d DUP5
    xs 0x411f (.reg (.dup 3)) (ri_dup (by rfl))  -- 411e DUP4
    xs 0x4120 (.reg .div) ri_div  -- 411f DIV
    xs 0x4121 (.reg .eq) ri_eq  -- 4120 EQ
    xs 0x4122 (.reg .or) ri_or  -- 4121 OR
    xs 0x4125 (.push [0x41, 0x2a] (by decide)) ri_push  -- 4122 PUSH2 0x412a
    xji 0x4126 0x412a hw
    · xdead
    have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x412b  -- 412a JUMPDEST
    xs 0x412c (.reg (.dup 0)) (ri_dup (by rfl))  -- 412b DUP1
    xs 0x412d (.reg (.swap 0)) (ri_swap (by rfl))  -- 412c SWAP1
    xs 0x412e (.reg .pop) ri_pop  -- 412d POP
    xs 0x412f (.reg (.swap 0)) (ri_swap (by rfl))  -- 412e SWAP1
    xs 0x4130 (.reg .pop) ri_pop  -- 412f POP
    xs 0x4131 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4130 SWAP1
    xs 0x4132 (.reg .pop) ri_pop  -- 4131 POP
    xs 0x4135 (.push [0x04, 0x00] (by decide)) ri_push  -- 4132 PUSH2 0x0400
    xl 0x4136 0x400  -- 4135 MLOAD
    xs 0x4137 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4136 DUP1
    xs 0x4138 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4137 DUP1
    xs 0x413b (.push [0x41, 0x40] (by decide)) ri_push  -- 4138 PUSH2 0x4140
    xji 0x413c 0x4140 hw
    · xdead
    have hd0 := hw
    clear hw
    xjd 0x4141  -- 4140 JUMPDEST
    xs 0x4142 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4141 DUP3
    xs 0x4143 (.reg .div) ri_div  -- 4142 DIV
    xs 0x4144 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4143 SWAP1
    xs 0x4145 (.reg .pop) ri_pop  -- 4144 POP
    xs 0x4146 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4145 SWAP1
    xs 0x4147 (.reg .pop) ri_pop  -- 4146 POP
    xs 0x4148 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4147 DUP1
    xs 0x4149 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4148 DUP3
    xs 0x414a (.reg .lt) ri_lt  -- 4149 LT
    xs 0x414b (.reg .iszero) ri_iszero  -- 414a ISZERO
    xs 0x414e (.push [0x41, 0x53] (by decide)) ri_push  -- 414b PUSH2 0x4153
    xji 0x414f 0x4153 hw
    · xdead
    have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0x4154  -- 4153 JUMPDEST
    xs 0x4155 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4154 DUP1
    xs 0x4156 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4155 DUP3
    xs 0x4157 (.reg .sub) ri_sub  -- 4156 SUB
    xs 0x4158 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4157 SWAP1
    xs 0x4159 (.reg .pop) ri_pop  -- 4158 POP
    xs 0x415a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4159 SWAP1
    xs 0x415b (.reg .pop) ri_pop  -- 415a POP
    xs 0x415e (.push [0x07, 0x40] (by decide)) ri_push  -- 415b PUSH2 0x0740
    xsw 0x415f 0x740  -- 415e MSTORE
    xjd 0x4160  -- 415f JUMPDEST
    xs 0x4163 (.push [0x05, 0x40] (by decide)) ri_push  -- 4160 PUSH2 0x0540
    xs 0x4166 (.push [0x07, 0x20] (by decide)) ri_push  -- 4163 PUSH2 0x0720
    xl 0x4167 0x720  -- 4166 MLOAD
    xs 0x4169 (.push [0x03] (by decide)) ri_push  -- 4167 PUSH1 0x03
    xs 0x416a (.reg (.dup 1)) (ri_dup (by rfl))  -- 4169 DUP2
    xs 0x416b (.reg .lt) ri_lt  -- 416a LT
    xs 0x416e (.push [0x41, 0x73] (by decide)) ri_push  -- 416b PUSH2 0x4173
    xji 0x416f 0x4173 hw
    · xdead
    clear hw
    xjd 0x4174  -- 4173 JUMPDEST
    xs 0x4176 (.push [0x20] (by decide)) ri_push  -- 4174 PUSH1 0x20
    xs 0x4177 (.reg .mul) ri_mul  -- 4176 MUL
    xs 0x4178 (.reg .add) ri_add  -- 4177 ADD
    xs 0x4179 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4178 DUP1
    xl 0x417a 0x540  -- 4179 MLOAD
    xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
    xl 0x417e 0x200  -- 417d MLOAD
    xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
    xl 0x4182 0x740  -- 4181 MLOAD
    xs 0x4183 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4182 DUP1
    xs 0x4184 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4183 DUP3
    xs 0x4185 (.reg .mul) ri_mul  -- 4184 MUL
    xs 0x4186 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4185 DUP3
    xs 0x4187 (.reg .iszero) ri_iszero  -- 4186 ISZERO
    xs 0x4188 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4187 DUP3
    xs 0x4189 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4188 DUP5
    xs 0x418a (.reg (.dup 3)) (ri_dup (by rfl))  -- 4189 DUP4
    xs 0x418b (.reg .div) ri_div  -- 418a DIV
    xs 0x418c (.reg .eq) ri_eq  -- 418b EQ
    xs 0x418d (.reg .or) ri_or  -- 418c OR
    xs 0x4190 (.push [0x41, 0x95] (by decide)) ri_push  -- 418d PUSH2 0x4195
    xji 0x4191 0x4195 hw
    · xdead
    have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x4196  -- 4195 JUMPDEST
    xs 0x4197 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4196 DUP1
    xs 0x4198 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4197 SWAP1
    xs 0x4199 (.reg .pop) ri_pop  -- 4198 POP
    xs 0x419a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4199 SWAP1
    xs 0x419b (.reg .pop) ri_pop  -- 419a POP
    xs 0x419c (.reg (.swap 0)) (ri_swap (by rfl))  -- 419b SWAP1
    xs 0x419d (.reg .pop) ri_pop  -- 419c POP
    xs 0x41a3 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 419d PUSH5 0x02540be400
    xs 0x41a4 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a3 DUP1
    xs 0x41a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a4 DUP1
    xs 0x41a8 (.push [0x41, 0xad] (by decide)) ri_push  -- 41a5 PUSH2 0x41ad
    xji 0x41a9 0x41ad hw
    · xdead
    clear hw
    xjd 0x41ae  -- 41ad JUMPDEST
    xs 0x41af (.reg (.dup 2)) (ri_dup (by rfl))  -- 41ae DUP3
    xs 0x41b0 (.reg .div) ri_div  -- 41af DIV
    xs 0x41b1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b0 SWAP1
    xs 0x41b2 (.reg .pop) ri_pop  -- 41b1 POP
    xs 0x41b3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b2 SWAP1
    xs 0x41b4 (.reg .pop) ri_pop  -- 41b3 POP
    xs 0x41b5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41b4 DUP1
    xs 0x41b6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41b5 DUP3
    xs 0x41b7 (.reg .lt) ri_lt  -- 41b6 LT
    xs 0x41b8 (.reg .iszero) ri_iszero  -- 41b7 ISZERO
    xs 0x41bb (.push [0x41, 0xc0] (by decide)) ri_push  -- 41b8 PUSH2 0x41c0
    xji 0x41bc 0x41c0 hw
    · xdead
    have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0x41c1  -- 41c0 JUMPDEST
    xs 0x41c2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41c1 DUP1
    xs 0x41c3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41c2 DUP3
    xs 0x41c4 (.reg .sub) ri_sub  -- 41c3 SUB
    xs 0x41c5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c4 SWAP1
    xs 0x41c6 (.reg .pop) ri_pop  -- 41c5 POP
    xs 0x41c7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c6 SWAP1
    xs 0x41c8 (.reg .pop) ri_pop  -- 41c7 POP
    xs 0x41c9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41c8 DUP2
    xsw 0x41ca 0x540  -- 41c9 MSTORE
    xs 0x41cb (.reg .pop) ri_pop  -- 41ca POP
    xjd 0x41cc  -- 41cb JUMPDEST
    xs 0x41cd (.reg (.dup 1)) (ri_dup (by rfl))  -- 41cc DUP2
    xl 0x41ce 0x720  -- 41cd MLOAD
    xs 0x41d0 (.push [0x01] (by decide)) ri_push  -- 41ce PUSH1 0x01
    xs 0x41d1 (.reg .add) ri_add  -- 41d0 ADD
    xs 0x41d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41d1 DUP1
    xs 0x41d3 (.reg (.dup 3)) (ri_dup (by rfl))  -- 41d2 DUP4
    xsw 0x41d4 0x720  -- 41d3 MSTORE
    xs 0x41d5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41d4 DUP2
    xs 0x41d6 (.reg .eq) ri_eq  -- 41d5 EQ
    xs 0x41d7 (.reg .iszero) ri_iszero  -- 41d6 ISZERO
    xs 0x41da (.push [0x40, 0x5e] (by decide)) ri_push  -- 41d7 PUSH2 0x405e
    xji 0x41db 0x405e hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, ⟨hm1, hd0, _, .inr ⟨hne, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
        simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have heq := eqCheck_ne_zero_eq (eqCheck_eq_zero hw)
  clear hw
  xs 0x4076 (.push [0x03, 0x20] (by decide)) ri_push  -- 4073 PUSH2 0x0320
  xs 0x4079 (.push [0x07, 0x20] (by decide)) ri_push  -- 4076 PUSH2 0x0720
  xl 0x407a 0x720  -- 4079 MLOAD
  xs 0x407c (.push [0x03] (by decide)) ri_push  -- 407a PUSH1 0x03
  xs 0x407d (.reg (.dup 1)) (ri_dup (by rfl))  -- 407c DUP2
  xs 0x407e (.reg .lt) ri_lt  -- 407d LT
  xs 0x4081 (.push [0x40, 0x86] (by decide)) ri_push  -- 407e PUSH2 0x4086
  xji 0x4082 0x4086 hw
  · xdead
  clear hw
  xjd 0x4087  -- 4086 JUMPDEST
  xs 0x4089 (.push [0x20] (by decide)) ri_push  -- 4087 PUSH1 0x20
  xs 0x408a (.reg .mul) ri_mul  -- 4089 MUL
  xs 0x408b (.reg .add) ri_add  -- 408a ADD
  xl 0x408c 0x320  -- 408b MLOAD
  xs 0x408f (.push [0x05, 0x20] (by decide)) ri_push  -- 408c PUSH2 0x0520
  xl 0x4090 0x520  -- 408f MLOAD
  xs 0x4091 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4090 DUP1
  xs 0x4092 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4091 DUP3
  xs 0x4093 (.reg .mul) ri_mul  -- 4092 MUL
  xs 0x4094 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4093 DUP3
  xs 0x4095 (.reg .iszero) ri_iszero  -- 4094 ISZERO
  xs 0x4096 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4095 DUP3
  xs 0x4097 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4096 DUP5
  xs 0x4098 (.reg (.dup 3)) (ri_dup (by rfl))  -- 4097 DUP4
  xs 0x4099 (.reg .div) ri_div  -- 4098 DIV
  xs 0x409a (.reg .eq) ri_eq  -- 4099 EQ
  xs 0x409b (.reg .or) ri_or  -- 409a OR
  xs 0x409e (.push [0x40, 0xa3] (by decide)) ri_push  -- 409b PUSH2 0x40a3
  xji 0x409f 0x40a3 hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x40a4  -- 40a3 JUMPDEST
  xs 0x40a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40a4 DUP1
  xs 0x40a6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a5 SWAP1
  xs 0x40a7 (.reg .pop) ri_pop  -- 40a6 POP
  xs 0x40a8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a7 SWAP1
  xs 0x40a9 (.reg .pop) ri_pop  -- 40a8 POP
  xs 0x40aa (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a9 SWAP1
  xs 0x40ab (.reg .pop) ri_pop  -- 40aa POP
  xs 0x40ae (.push [0x04, 0x00] (by decide)) ri_push  -- 40ab PUSH2 0x0400
  xl 0x40af 0x400  -- 40ae MLOAD
  xs 0x40b0 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40af DUP1
  xs 0x40b1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40b0 DUP1
  xs 0x40b4 (.push [0x40, 0xb9] (by decide)) ri_push  -- 40b1 PUSH2 0x40b9
  xji 0x40b5 0x40b9 hw
  · xdead
  have hd0 := hw
  clear hw
  xjd 0x40ba  -- 40b9 JUMPDEST
  xs 0x40bb (.reg (.dup 2)) (ri_dup (by rfl))  -- 40ba DUP3
  xs 0x40bc (.reg .div) ri_div  -- 40bb DIV
  xs 0x40bd (.reg (.swap 0)) (ri_swap (by rfl))  -- 40bc SWAP1
  xs 0x40be (.reg .pop) ri_pop  -- 40bd POP
  xs 0x40bf (.reg (.swap 0)) (ri_swap (by rfl))  -- 40be SWAP1
  xs 0x40c0 (.reg .pop) ri_pop  -- 40bf POP
  xs 0x40c3 (.push [0x05, 0xa0] (by decide)) ri_push  -- 40c0 PUSH2 0x05a0
  xl 0x40c4 0x5a0  -- 40c3 MLOAD
  xs 0x40c5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40c4 DUP1
  xs 0x40c6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 40c5 DUP3
  xs 0x40c7 (.reg .lt) ri_lt  -- 40c6 LT
  xs 0x40c8 (.reg .iszero) ri_iszero  -- 40c7 ISZERO
  xs 0x40cb (.push [0x40, 0xd0] (by decide)) ri_push  -- 40c8 PUSH2 0x40d0
  xji 0x40cc 0x40d0 hw
  · xdead
  have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x40d1  -- 40d0 JUMPDEST
  xs 0x40d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40d1 DUP1
  xs 0x40d3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 40d2 DUP3
  xs 0x40d4 (.reg .sub) ri_sub  -- 40d3 SUB
  xs 0x40d5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40d4 SWAP1
  xs 0x40d6 (.reg .pop) ri_pop  -- 40d5 POP
  xs 0x40d7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40d6 SWAP1
  xs 0x40d8 (.reg .pop) ri_pop  -- 40d7 POP
  xs 0x40db (.push [0x07, 0x40] (by decide)) ri_push  -- 40d8 PUSH2 0x0740
  xsw 0x40dc 0x740  -- 40db MSTORE
  xs 0x40df (.push [0x41, 0x5f] (by decide)) ri_push  -- 40dc PUSH2 0x415f
  xjmp 0x415f  -- 40df JUMP
  xjd 0x4160  -- 415f JUMPDEST
  xs 0x4163 (.push [0x05, 0x40] (by decide)) ri_push  -- 4160 PUSH2 0x0540
  xs 0x4166 (.push [0x07, 0x20] (by decide)) ri_push  -- 4163 PUSH2 0x0720
  xl 0x4167 0x720  -- 4166 MLOAD
  xs 0x4169 (.push [0x03] (by decide)) ri_push  -- 4167 PUSH1 0x03
  xs 0x416a (.reg (.dup 1)) (ri_dup (by rfl))  -- 4169 DUP2
  xs 0x416b (.reg .lt) ri_lt  -- 416a LT
  xs 0x416e (.push [0x41, 0x73] (by decide)) ri_push  -- 416b PUSH2 0x4173
  xji 0x416f 0x4173 hw
  · xdead
  clear hw
  xjd 0x4174  -- 4173 JUMPDEST
  xs 0x4176 (.push [0x20] (by decide)) ri_push  -- 4174 PUSH1 0x20
  xs 0x4177 (.reg .mul) ri_mul  -- 4176 MUL
  xs 0x4178 (.reg .add) ri_add  -- 4177 ADD
  xs 0x4179 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4178 DUP1
  xl 0x417a 0x540  -- 4179 MLOAD
  xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
  xl 0x417e 0x200  -- 417d MLOAD
  xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
  xl 0x4182 0x740  -- 4181 MLOAD
  xs 0x4183 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4182 DUP1
  xs 0x4184 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4183 DUP3
  xs 0x4185 (.reg .mul) ri_mul  -- 4184 MUL
  xs 0x4186 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4185 DUP3
  xs 0x4187 (.reg .iszero) ri_iszero  -- 4186 ISZERO
  xs 0x4188 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4187 DUP3
  xs 0x4189 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4188 DUP5
  xs 0x418a (.reg (.dup 3)) (ri_dup (by rfl))  -- 4189 DUP4
  xs 0x418b (.reg .div) ri_div  -- 418a DIV
  xs 0x418c (.reg .eq) ri_eq  -- 418b EQ
  xs 0x418d (.reg .or) ri_or  -- 418c OR
  xs 0x4190 (.push [0x41, 0x95] (by decide)) ri_push  -- 418d PUSH2 0x4195
  xji 0x4191 0x4195 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x4196  -- 4195 JUMPDEST
  xs 0x4197 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4196 DUP1
  xs 0x4198 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4197 SWAP1
  xs 0x4199 (.reg .pop) ri_pop  -- 4198 POP
  xs 0x419a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4199 SWAP1
  xs 0x419b (.reg .pop) ri_pop  -- 419a POP
  xs 0x419c (.reg (.swap 0)) (ri_swap (by rfl))  -- 419b SWAP1
  xs 0x419d (.reg .pop) ri_pop  -- 419c POP
  xs 0x41a3 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 419d PUSH5 0x02540be400
  xs 0x41a4 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a3 DUP1
  xs 0x41a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a4 DUP1
  xs 0x41a8 (.push [0x41, 0xad] (by decide)) ri_push  -- 41a5 PUSH2 0x41ad
  xji 0x41a9 0x41ad hw
  · xdead
  clear hw
  xjd 0x41ae  -- 41ad JUMPDEST
  xs 0x41af (.reg (.dup 2)) (ri_dup (by rfl))  -- 41ae DUP3
  xs 0x41b0 (.reg .div) ri_div  -- 41af DIV
  xs 0x41b1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b0 SWAP1
  xs 0x41b2 (.reg .pop) ri_pop  -- 41b1 POP
  xs 0x41b3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b2 SWAP1
  xs 0x41b4 (.reg .pop) ri_pop  -- 41b3 POP
  xs 0x41b5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41b4 DUP1
  xs 0x41b6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41b5 DUP3
  xs 0x41b7 (.reg .lt) ri_lt  -- 41b6 LT
  xs 0x41b8 (.reg .iszero) ri_iszero  -- 41b7 ISZERO
  xs 0x41bb (.push [0x41, 0xc0] (by decide)) ri_push  -- 41b8 PUSH2 0x41c0
  xji 0x41bc 0x41c0 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x41c1  -- 41c0 JUMPDEST
  xs 0x41c2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41c1 DUP1
  xs 0x41c3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41c2 DUP3
  xs 0x41c4 (.reg .sub) ri_sub  -- 41c3 SUB
  xs 0x41c5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c4 SWAP1
  xs 0x41c6 (.reg .pop) ri_pop  -- 41c5 POP
  xs 0x41c7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c6 SWAP1
  xs 0x41c8 (.reg .pop) ri_pop  -- 41c7 POP
  xs 0x41c9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41c8 DUP2
  xsw 0x41ca 0x540  -- 41c9 MSTORE
  xs 0x41cb (.reg .pop) ri_pop  -- 41ca POP
  xjd 0x41cc  -- 41cb JUMPDEST
  xs 0x41cd (.reg (.dup 1)) (ri_dup (by rfl))  -- 41cc DUP2
  xl 0x41ce 0x720  -- 41cd MLOAD
  xs 0x41d0 (.push [0x01] (by decide)) ri_push  -- 41ce PUSH1 0x01
  xs 0x41d1 (.reg .add) ri_add  -- 41d0 ADD
  xs 0x41d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41d1 DUP1
  xs 0x41d3 (.reg (.dup 3)) (ri_dup (by rfl))  -- 41d2 DUP4
  xsw 0x41d4 0x720  -- 41d3 MSTORE
  xs 0x41d5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41d4 DUP2
  xs 0x41d6 (.reg .eq) ri_eq  -- 41d5 EQ
  xs 0x41d7 (.reg .iszero) ri_iszero  -- 41d6 ISZERO
  xs 0x41da (.push [0x40, 0x5e] (by decide)) ri_push  -- 41d7 PUSH2 0x405e
  xji 0x41db 0x405e hw
  · exact absurd hw (by decide)
  exact ⟨_, _, _, ⟨hm1, hd0, _, .inl ⟨heq, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩


/-- **Fee-loop iteration 1.** -/
theorem xa_cw_it1 {M : Mem} {a i A F T x0 x1 x2 D0 D1 y dy0 r0 r1 r2 ck : B256}
    (hcode : sevm.code = code) (hck : ck = Bytes.toB256 [1])
    (hV : VW M [(0x720, ck), (0x700, dy0), (0x5a0, y), (0x580, r2), (0x560, r1),
        (0x540, r0), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)])
    (h : XAt sevm post 0x405e
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G) L) :
    ∃ r' M' G', CwStep (Bytes.toB256 [1] = i) x1 D1 D0 y F r1 r' ∧
      XAt sevm post 0x405e
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' G') L ∧
      VW M' [(0x720, Bytes.toB256 [1] + Bytes.toB256 [1]), (0x700, dy0), (0x5a0, y), (0x580, r2), (0x560, r'),
        (0x540, r0), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)] := by
  subst hck
  xjd 0x405f  -- 405e JUMPDEST
  xs 0x4061 (.push [0x00] (by decide)) ri_push  -- 405f PUSH1 0x00
  xs 0x4064 (.push [0x07, 0x40] (by decide)) ri_push  -- 4061 PUSH2 0x0740
  xsw 0x4065 0x740  -- 4064 MSTORE
  xs 0x4068 (.push [0x01, 0x60] (by decide)) ri_push  -- 4065 PUSH2 0x0160
  xl 0x4069 0x160  -- 4068 MLOAD
  xs 0x406c (.push [0x07, 0x20] (by decide)) ri_push  -- 4069 PUSH2 0x0720
  xl 0x406d 0x720  -- 406c MLOAD
  xs 0x406e (.reg .eq) ri_eq  -- 406d EQ
  xs 0x406f (.reg .iszero) ri_iszero  -- 406e ISZERO
  xs 0x4072 (.push [0x40, 0xe0] (by decide)) ri_push  -- 406f PUSH2 0x40e0
  xji 0x4073 0x40e0 hw
  swap
  · have hne := eqCheck_eq_zero (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x40e1  -- 40e0 JUMPDEST
    xs 0x40e4 (.push [0x03, 0x20] (by decide)) ri_push  -- 40e1 PUSH2 0x0320
    xs 0x40e7 (.push [0x07, 0x20] (by decide)) ri_push  -- 40e4 PUSH2 0x0720
    xl 0x40e8 0x720  -- 40e7 MLOAD
    xs 0x40ea (.push [0x03] (by decide)) ri_push  -- 40e8 PUSH1 0x03
    xs 0x40eb (.reg (.dup 1)) (ri_dup (by rfl))  -- 40ea DUP2
    xs 0x40ec (.reg .lt) ri_lt  -- 40eb LT
    xs 0x40ef (.push [0x40, 0xf4] (by decide)) ri_push  -- 40ec PUSH2 0x40f4
    xji 0x40f0 0x40f4 hw
    · xdead
    clear hw
    xjd 0x40f5  -- 40f4 JUMPDEST
    xs 0x40f7 (.push [0x20] (by decide)) ri_push  -- 40f5 PUSH1 0x20
    xs 0x40f8 (.reg .mul) ri_mul  -- 40f7 MUL
    xs 0x40f9 (.reg .add) ri_add  -- 40f8 ADD
    xl 0x40fa 0x340  -- 40f9 MLOAD
    xs 0x40fd (.push [0x03, 0x20] (by decide)) ri_push  -- 40fa PUSH2 0x0320
    xs 0x4100 (.push [0x07, 0x20] (by decide)) ri_push  -- 40fd PUSH2 0x0720
    xl 0x4101 0x720  -- 4100 MLOAD
    xs 0x4103 (.push [0x03] (by decide)) ri_push  -- 4101 PUSH1 0x03
    xs 0x4104 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4103 DUP2
    xs 0x4105 (.reg .lt) ri_lt  -- 4104 LT
    xs 0x4108 (.push [0x41, 0x0d] (by decide)) ri_push  -- 4105 PUSH2 0x410d
    xji 0x4109 0x410d hw
    · xdead
    clear hw
    xjd 0x410e  -- 410d JUMPDEST
    xs 0x4110 (.push [0x20] (by decide)) ri_push  -- 410e PUSH1 0x20
    xs 0x4111 (.reg .mul) ri_mul  -- 4110 MUL
    xs 0x4112 (.reg .add) ri_add  -- 4111 ADD
    xl 0x4113 0x340  -- 4112 MLOAD
    xs 0x4116 (.push [0x05, 0x20] (by decide)) ri_push  -- 4113 PUSH2 0x0520
    xl 0x4117 0x520  -- 4116 MLOAD
    xs 0x4118 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4117 DUP1
    xs 0x4119 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4118 DUP3
    xs 0x411a (.reg .mul) ri_mul  -- 4119 MUL
    xs 0x411b (.reg (.dup 2)) (ri_dup (by rfl))  -- 411a DUP3
    xs 0x411c (.reg .iszero) ri_iszero  -- 411b ISZERO
    xs 0x411d (.reg (.dup 2)) (ri_dup (by rfl))  -- 411c DUP3
    xs 0x411e (.reg (.dup 4)) (ri_dup (by rfl))  -- 411d DUP5
    xs 0x411f (.reg (.dup 3)) (ri_dup (by rfl))  -- 411e DUP4
    xs 0x4120 (.reg .div) ri_div  -- 411f DIV
    xs 0x4121 (.reg .eq) ri_eq  -- 4120 EQ
    xs 0x4122 (.reg .or) ri_or  -- 4121 OR
    xs 0x4125 (.push [0x41, 0x2a] (by decide)) ri_push  -- 4122 PUSH2 0x412a
    xji 0x4126 0x412a hw
    · xdead
    have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x412b  -- 412a JUMPDEST
    xs 0x412c (.reg (.dup 0)) (ri_dup (by rfl))  -- 412b DUP1
    xs 0x412d (.reg (.swap 0)) (ri_swap (by rfl))  -- 412c SWAP1
    xs 0x412e (.reg .pop) ri_pop  -- 412d POP
    xs 0x412f (.reg (.swap 0)) (ri_swap (by rfl))  -- 412e SWAP1
    xs 0x4130 (.reg .pop) ri_pop  -- 412f POP
    xs 0x4131 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4130 SWAP1
    xs 0x4132 (.reg .pop) ri_pop  -- 4131 POP
    xs 0x4135 (.push [0x04, 0x00] (by decide)) ri_push  -- 4132 PUSH2 0x0400
    xl 0x4136 0x400  -- 4135 MLOAD
    xs 0x4137 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4136 DUP1
    xs 0x4138 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4137 DUP1
    xs 0x413b (.push [0x41, 0x40] (by decide)) ri_push  -- 4138 PUSH2 0x4140
    xji 0x413c 0x4140 hw
    · xdead
    have hd0 := hw
    clear hw
    xjd 0x4141  -- 4140 JUMPDEST
    xs 0x4142 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4141 DUP3
    xs 0x4143 (.reg .div) ri_div  -- 4142 DIV
    xs 0x4144 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4143 SWAP1
    xs 0x4145 (.reg .pop) ri_pop  -- 4144 POP
    xs 0x4146 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4145 SWAP1
    xs 0x4147 (.reg .pop) ri_pop  -- 4146 POP
    xs 0x4148 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4147 DUP1
    xs 0x4149 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4148 DUP3
    xs 0x414a (.reg .lt) ri_lt  -- 4149 LT
    xs 0x414b (.reg .iszero) ri_iszero  -- 414a ISZERO
    xs 0x414e (.push [0x41, 0x53] (by decide)) ri_push  -- 414b PUSH2 0x4153
    xji 0x414f 0x4153 hw
    · xdead
    have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0x4154  -- 4153 JUMPDEST
    xs 0x4155 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4154 DUP1
    xs 0x4156 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4155 DUP3
    xs 0x4157 (.reg .sub) ri_sub  -- 4156 SUB
    xs 0x4158 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4157 SWAP1
    xs 0x4159 (.reg .pop) ri_pop  -- 4158 POP
    xs 0x415a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4159 SWAP1
    xs 0x415b (.reg .pop) ri_pop  -- 415a POP
    xs 0x415e (.push [0x07, 0x40] (by decide)) ri_push  -- 415b PUSH2 0x0740
    xsw 0x415f 0x740  -- 415e MSTORE
    xjd 0x4160  -- 415f JUMPDEST
    xs 0x4163 (.push [0x05, 0x40] (by decide)) ri_push  -- 4160 PUSH2 0x0540
    xs 0x4166 (.push [0x07, 0x20] (by decide)) ri_push  -- 4163 PUSH2 0x0720
    xl 0x4167 0x720  -- 4166 MLOAD
    xs 0x4169 (.push [0x03] (by decide)) ri_push  -- 4167 PUSH1 0x03
    xs 0x416a (.reg (.dup 1)) (ri_dup (by rfl))  -- 4169 DUP2
    xs 0x416b (.reg .lt) ri_lt  -- 416a LT
    xs 0x416e (.push [0x41, 0x73] (by decide)) ri_push  -- 416b PUSH2 0x4173
    xji 0x416f 0x4173 hw
    · xdead
    clear hw
    xjd 0x4174  -- 4173 JUMPDEST
    xs 0x4176 (.push [0x20] (by decide)) ri_push  -- 4174 PUSH1 0x20
    xs 0x4177 (.reg .mul) ri_mul  -- 4176 MUL
    xs 0x4178 (.reg .add) ri_add  -- 4177 ADD
    xs 0x4179 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4178 DUP1
    xl 0x417a 0x560  -- 4179 MLOAD
    xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
    xl 0x417e 0x200  -- 417d MLOAD
    xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
    xl 0x4182 0x740  -- 4181 MLOAD
    xs 0x4183 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4182 DUP1
    xs 0x4184 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4183 DUP3
    xs 0x4185 (.reg .mul) ri_mul  -- 4184 MUL
    xs 0x4186 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4185 DUP3
    xs 0x4187 (.reg .iszero) ri_iszero  -- 4186 ISZERO
    xs 0x4188 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4187 DUP3
    xs 0x4189 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4188 DUP5
    xs 0x418a (.reg (.dup 3)) (ri_dup (by rfl))  -- 4189 DUP4
    xs 0x418b (.reg .div) ri_div  -- 418a DIV
    xs 0x418c (.reg .eq) ri_eq  -- 418b EQ
    xs 0x418d (.reg .or) ri_or  -- 418c OR
    xs 0x4190 (.push [0x41, 0x95] (by decide)) ri_push  -- 418d PUSH2 0x4195
    xji 0x4191 0x4195 hw
    · xdead
    have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x4196  -- 4195 JUMPDEST
    xs 0x4197 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4196 DUP1
    xs 0x4198 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4197 SWAP1
    xs 0x4199 (.reg .pop) ri_pop  -- 4198 POP
    xs 0x419a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4199 SWAP1
    xs 0x419b (.reg .pop) ri_pop  -- 419a POP
    xs 0x419c (.reg (.swap 0)) (ri_swap (by rfl))  -- 419b SWAP1
    xs 0x419d (.reg .pop) ri_pop  -- 419c POP
    xs 0x41a3 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 419d PUSH5 0x02540be400
    xs 0x41a4 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a3 DUP1
    xs 0x41a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a4 DUP1
    xs 0x41a8 (.push [0x41, 0xad] (by decide)) ri_push  -- 41a5 PUSH2 0x41ad
    xji 0x41a9 0x41ad hw
    · xdead
    clear hw
    xjd 0x41ae  -- 41ad JUMPDEST
    xs 0x41af (.reg (.dup 2)) (ri_dup (by rfl))  -- 41ae DUP3
    xs 0x41b0 (.reg .div) ri_div  -- 41af DIV
    xs 0x41b1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b0 SWAP1
    xs 0x41b2 (.reg .pop) ri_pop  -- 41b1 POP
    xs 0x41b3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b2 SWAP1
    xs 0x41b4 (.reg .pop) ri_pop  -- 41b3 POP
    xs 0x41b5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41b4 DUP1
    xs 0x41b6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41b5 DUP3
    xs 0x41b7 (.reg .lt) ri_lt  -- 41b6 LT
    xs 0x41b8 (.reg .iszero) ri_iszero  -- 41b7 ISZERO
    xs 0x41bb (.push [0x41, 0xc0] (by decide)) ri_push  -- 41b8 PUSH2 0x41c0
    xji 0x41bc 0x41c0 hw
    · xdead
    have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0x41c1  -- 41c0 JUMPDEST
    xs 0x41c2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41c1 DUP1
    xs 0x41c3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41c2 DUP3
    xs 0x41c4 (.reg .sub) ri_sub  -- 41c3 SUB
    xs 0x41c5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c4 SWAP1
    xs 0x41c6 (.reg .pop) ri_pop  -- 41c5 POP
    xs 0x41c7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c6 SWAP1
    xs 0x41c8 (.reg .pop) ri_pop  -- 41c7 POP
    xs 0x41c9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41c8 DUP2
    xsw 0x41ca 0x560  -- 41c9 MSTORE
    xs 0x41cb (.reg .pop) ri_pop  -- 41ca POP
    xjd 0x41cc  -- 41cb JUMPDEST
    xs 0x41cd (.reg (.dup 1)) (ri_dup (by rfl))  -- 41cc DUP2
    xl 0x41ce 0x720  -- 41cd MLOAD
    xs 0x41d0 (.push [0x01] (by decide)) ri_push  -- 41ce PUSH1 0x01
    xs 0x41d1 (.reg .add) ri_add  -- 41d0 ADD
    xs 0x41d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41d1 DUP1
    xs 0x41d3 (.reg (.dup 3)) (ri_dup (by rfl))  -- 41d2 DUP4
    xsw 0x41d4 0x720  -- 41d3 MSTORE
    xs 0x41d5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41d4 DUP2
    xs 0x41d6 (.reg .eq) ri_eq  -- 41d5 EQ
    xs 0x41d7 (.reg .iszero) ri_iszero  -- 41d6 ISZERO
    xs 0x41da (.push [0x40, 0x5e] (by decide)) ri_push  -- 41d7 PUSH2 0x405e
    xji 0x41db 0x405e hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, ⟨hm1, hd0, _, .inr ⟨hne, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
        simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have heq := eqCheck_ne_zero_eq (eqCheck_eq_zero hw)
  clear hw
  xs 0x4076 (.push [0x03, 0x20] (by decide)) ri_push  -- 4073 PUSH2 0x0320
  xs 0x4079 (.push [0x07, 0x20] (by decide)) ri_push  -- 4076 PUSH2 0x0720
  xl 0x407a 0x720  -- 4079 MLOAD
  xs 0x407c (.push [0x03] (by decide)) ri_push  -- 407a PUSH1 0x03
  xs 0x407d (.reg (.dup 1)) (ri_dup (by rfl))  -- 407c DUP2
  xs 0x407e (.reg .lt) ri_lt  -- 407d LT
  xs 0x4081 (.push [0x40, 0x86] (by decide)) ri_push  -- 407e PUSH2 0x4086
  xji 0x4082 0x4086 hw
  · xdead
  clear hw
  xjd 0x4087  -- 4086 JUMPDEST
  xs 0x4089 (.push [0x20] (by decide)) ri_push  -- 4087 PUSH1 0x20
  xs 0x408a (.reg .mul) ri_mul  -- 4089 MUL
  xs 0x408b (.reg .add) ri_add  -- 408a ADD
  xl 0x408c 0x340  -- 408b MLOAD
  xs 0x408f (.push [0x05, 0x20] (by decide)) ri_push  -- 408c PUSH2 0x0520
  xl 0x4090 0x520  -- 408f MLOAD
  xs 0x4091 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4090 DUP1
  xs 0x4092 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4091 DUP3
  xs 0x4093 (.reg .mul) ri_mul  -- 4092 MUL
  xs 0x4094 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4093 DUP3
  xs 0x4095 (.reg .iszero) ri_iszero  -- 4094 ISZERO
  xs 0x4096 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4095 DUP3
  xs 0x4097 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4096 DUP5
  xs 0x4098 (.reg (.dup 3)) (ri_dup (by rfl))  -- 4097 DUP4
  xs 0x4099 (.reg .div) ri_div  -- 4098 DIV
  xs 0x409a (.reg .eq) ri_eq  -- 4099 EQ
  xs 0x409b (.reg .or) ri_or  -- 409a OR
  xs 0x409e (.push [0x40, 0xa3] (by decide)) ri_push  -- 409b PUSH2 0x40a3
  xji 0x409f 0x40a3 hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x40a4  -- 40a3 JUMPDEST
  xs 0x40a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40a4 DUP1
  xs 0x40a6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a5 SWAP1
  xs 0x40a7 (.reg .pop) ri_pop  -- 40a6 POP
  xs 0x40a8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a7 SWAP1
  xs 0x40a9 (.reg .pop) ri_pop  -- 40a8 POP
  xs 0x40aa (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a9 SWAP1
  xs 0x40ab (.reg .pop) ri_pop  -- 40aa POP
  xs 0x40ae (.push [0x04, 0x00] (by decide)) ri_push  -- 40ab PUSH2 0x0400
  xl 0x40af 0x400  -- 40ae MLOAD
  xs 0x40b0 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40af DUP1
  xs 0x40b1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40b0 DUP1
  xs 0x40b4 (.push [0x40, 0xb9] (by decide)) ri_push  -- 40b1 PUSH2 0x40b9
  xji 0x40b5 0x40b9 hw
  · xdead
  have hd0 := hw
  clear hw
  xjd 0x40ba  -- 40b9 JUMPDEST
  xs 0x40bb (.reg (.dup 2)) (ri_dup (by rfl))  -- 40ba DUP3
  xs 0x40bc (.reg .div) ri_div  -- 40bb DIV
  xs 0x40bd (.reg (.swap 0)) (ri_swap (by rfl))  -- 40bc SWAP1
  xs 0x40be (.reg .pop) ri_pop  -- 40bd POP
  xs 0x40bf (.reg (.swap 0)) (ri_swap (by rfl))  -- 40be SWAP1
  xs 0x40c0 (.reg .pop) ri_pop  -- 40bf POP
  xs 0x40c3 (.push [0x05, 0xa0] (by decide)) ri_push  -- 40c0 PUSH2 0x05a0
  xl 0x40c4 0x5a0  -- 40c3 MLOAD
  xs 0x40c5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40c4 DUP1
  xs 0x40c6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 40c5 DUP3
  xs 0x40c7 (.reg .lt) ri_lt  -- 40c6 LT
  xs 0x40c8 (.reg .iszero) ri_iszero  -- 40c7 ISZERO
  xs 0x40cb (.push [0x40, 0xd0] (by decide)) ri_push  -- 40c8 PUSH2 0x40d0
  xji 0x40cc 0x40d0 hw
  · xdead
  have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x40d1  -- 40d0 JUMPDEST
  xs 0x40d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40d1 DUP1
  xs 0x40d3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 40d2 DUP3
  xs 0x40d4 (.reg .sub) ri_sub  -- 40d3 SUB
  xs 0x40d5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40d4 SWAP1
  xs 0x40d6 (.reg .pop) ri_pop  -- 40d5 POP
  xs 0x40d7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40d6 SWAP1
  xs 0x40d8 (.reg .pop) ri_pop  -- 40d7 POP
  xs 0x40db (.push [0x07, 0x40] (by decide)) ri_push  -- 40d8 PUSH2 0x0740
  xsw 0x40dc 0x740  -- 40db MSTORE
  xs 0x40df (.push [0x41, 0x5f] (by decide)) ri_push  -- 40dc PUSH2 0x415f
  xjmp 0x415f  -- 40df JUMP
  xjd 0x4160  -- 415f JUMPDEST
  xs 0x4163 (.push [0x05, 0x40] (by decide)) ri_push  -- 4160 PUSH2 0x0540
  xs 0x4166 (.push [0x07, 0x20] (by decide)) ri_push  -- 4163 PUSH2 0x0720
  xl 0x4167 0x720  -- 4166 MLOAD
  xs 0x4169 (.push [0x03] (by decide)) ri_push  -- 4167 PUSH1 0x03
  xs 0x416a (.reg (.dup 1)) (ri_dup (by rfl))  -- 4169 DUP2
  xs 0x416b (.reg .lt) ri_lt  -- 416a LT
  xs 0x416e (.push [0x41, 0x73] (by decide)) ri_push  -- 416b PUSH2 0x4173
  xji 0x416f 0x4173 hw
  · xdead
  clear hw
  xjd 0x4174  -- 4173 JUMPDEST
  xs 0x4176 (.push [0x20] (by decide)) ri_push  -- 4174 PUSH1 0x20
  xs 0x4177 (.reg .mul) ri_mul  -- 4176 MUL
  xs 0x4178 (.reg .add) ri_add  -- 4177 ADD
  xs 0x4179 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4178 DUP1
  xl 0x417a 0x560  -- 4179 MLOAD
  xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
  xl 0x417e 0x200  -- 417d MLOAD
  xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
  xl 0x4182 0x740  -- 4181 MLOAD
  xs 0x4183 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4182 DUP1
  xs 0x4184 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4183 DUP3
  xs 0x4185 (.reg .mul) ri_mul  -- 4184 MUL
  xs 0x4186 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4185 DUP3
  xs 0x4187 (.reg .iszero) ri_iszero  -- 4186 ISZERO
  xs 0x4188 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4187 DUP3
  xs 0x4189 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4188 DUP5
  xs 0x418a (.reg (.dup 3)) (ri_dup (by rfl))  -- 4189 DUP4
  xs 0x418b (.reg .div) ri_div  -- 418a DIV
  xs 0x418c (.reg .eq) ri_eq  -- 418b EQ
  xs 0x418d (.reg .or) ri_or  -- 418c OR
  xs 0x4190 (.push [0x41, 0x95] (by decide)) ri_push  -- 418d PUSH2 0x4195
  xji 0x4191 0x4195 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x4196  -- 4195 JUMPDEST
  xs 0x4197 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4196 DUP1
  xs 0x4198 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4197 SWAP1
  xs 0x4199 (.reg .pop) ri_pop  -- 4198 POP
  xs 0x419a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4199 SWAP1
  xs 0x419b (.reg .pop) ri_pop  -- 419a POP
  xs 0x419c (.reg (.swap 0)) (ri_swap (by rfl))  -- 419b SWAP1
  xs 0x419d (.reg .pop) ri_pop  -- 419c POP
  xs 0x41a3 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 419d PUSH5 0x02540be400
  xs 0x41a4 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a3 DUP1
  xs 0x41a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a4 DUP1
  xs 0x41a8 (.push [0x41, 0xad] (by decide)) ri_push  -- 41a5 PUSH2 0x41ad
  xji 0x41a9 0x41ad hw
  · xdead
  clear hw
  xjd 0x41ae  -- 41ad JUMPDEST
  xs 0x41af (.reg (.dup 2)) (ri_dup (by rfl))  -- 41ae DUP3
  xs 0x41b0 (.reg .div) ri_div  -- 41af DIV
  xs 0x41b1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b0 SWAP1
  xs 0x41b2 (.reg .pop) ri_pop  -- 41b1 POP
  xs 0x41b3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b2 SWAP1
  xs 0x41b4 (.reg .pop) ri_pop  -- 41b3 POP
  xs 0x41b5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41b4 DUP1
  xs 0x41b6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41b5 DUP3
  xs 0x41b7 (.reg .lt) ri_lt  -- 41b6 LT
  xs 0x41b8 (.reg .iszero) ri_iszero  -- 41b7 ISZERO
  xs 0x41bb (.push [0x41, 0xc0] (by decide)) ri_push  -- 41b8 PUSH2 0x41c0
  xji 0x41bc 0x41c0 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x41c1  -- 41c0 JUMPDEST
  xs 0x41c2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41c1 DUP1
  xs 0x41c3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41c2 DUP3
  xs 0x41c4 (.reg .sub) ri_sub  -- 41c3 SUB
  xs 0x41c5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c4 SWAP1
  xs 0x41c6 (.reg .pop) ri_pop  -- 41c5 POP
  xs 0x41c7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c6 SWAP1
  xs 0x41c8 (.reg .pop) ri_pop  -- 41c7 POP
  xs 0x41c9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41c8 DUP2
  xsw 0x41ca 0x560  -- 41c9 MSTORE
  xs 0x41cb (.reg .pop) ri_pop  -- 41ca POP
  xjd 0x41cc  -- 41cb JUMPDEST
  xs 0x41cd (.reg (.dup 1)) (ri_dup (by rfl))  -- 41cc DUP2
  xl 0x41ce 0x720  -- 41cd MLOAD
  xs 0x41d0 (.push [0x01] (by decide)) ri_push  -- 41ce PUSH1 0x01
  xs 0x41d1 (.reg .add) ri_add  -- 41d0 ADD
  xs 0x41d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41d1 DUP1
  xs 0x41d3 (.reg (.dup 3)) (ri_dup (by rfl))  -- 41d2 DUP4
  xsw 0x41d4 0x720  -- 41d3 MSTORE
  xs 0x41d5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41d4 DUP2
  xs 0x41d6 (.reg .eq) ri_eq  -- 41d5 EQ
  xs 0x41d7 (.reg .iszero) ri_iszero  -- 41d6 ISZERO
  xs 0x41da (.push [0x40, 0x5e] (by decide)) ri_push  -- 41d7 PUSH2 0x405e
  xji 0x41db 0x405e hw
  · exact absurd hw (by decide)
  exact ⟨_, _, _, ⟨hm1, hd0, _, .inl ⟨heq, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩


/-- **Fee-loop iteration 2.** -/
theorem xa_cw_it2 {M : Mem} {a i A F T x0 x1 x2 D0 D1 y dy0 r0 r1 r2 ck : B256}
    (hcode : sevm.code = code) (hck : ck = Bytes.toB256 [2])
    (hV : VW M [(0x720, ck), (0x700, dy0), (0x5a0, y), (0x580, r2), (0x560, r1),
        (0x540, r0), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)])
    (h : XAt sevm post 0x405e
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G) L) :
    ∃ r' M' G', CwStep (Bytes.toB256 [2] = i) x2 D1 D0 y F r2 r' ∧
      XAt sevm post 0x41db
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' G') L ∧
      VW M' [(0x720, Bytes.toB256 [1] + Bytes.toB256 [2]), (0x700, dy0), (0x5a0, y), (0x580, r'), (0x560, r1),
        (0x540, r0), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)] := by
  subst hck
  xjd 0x405f  -- 405e JUMPDEST
  xs 0x4061 (.push [0x00] (by decide)) ri_push  -- 405f PUSH1 0x00
  xs 0x4064 (.push [0x07, 0x40] (by decide)) ri_push  -- 4061 PUSH2 0x0740
  xsw 0x4065 0x740  -- 4064 MSTORE
  xs 0x4068 (.push [0x01, 0x60] (by decide)) ri_push  -- 4065 PUSH2 0x0160
  xl 0x4069 0x160  -- 4068 MLOAD
  xs 0x406c (.push [0x07, 0x20] (by decide)) ri_push  -- 4069 PUSH2 0x0720
  xl 0x406d 0x720  -- 406c MLOAD
  xs 0x406e (.reg .eq) ri_eq  -- 406d EQ
  xs 0x406f (.reg .iszero) ri_iszero  -- 406e ISZERO
  xs 0x4072 (.push [0x40, 0xe0] (by decide)) ri_push  -- 406f PUSH2 0x40e0
  xji 0x4073 0x40e0 hw
  swap
  · have hne := eqCheck_eq_zero (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x40e1  -- 40e0 JUMPDEST
    xs 0x40e4 (.push [0x03, 0x20] (by decide)) ri_push  -- 40e1 PUSH2 0x0320
    xs 0x40e7 (.push [0x07, 0x20] (by decide)) ri_push  -- 40e4 PUSH2 0x0720
    xl 0x40e8 0x720  -- 40e7 MLOAD
    xs 0x40ea (.push [0x03] (by decide)) ri_push  -- 40e8 PUSH1 0x03
    xs 0x40eb (.reg (.dup 1)) (ri_dup (by rfl))  -- 40ea DUP2
    xs 0x40ec (.reg .lt) ri_lt  -- 40eb LT
    xs 0x40ef (.push [0x40, 0xf4] (by decide)) ri_push  -- 40ec PUSH2 0x40f4
    xji 0x40f0 0x40f4 hw
    · xdead
    clear hw
    xjd 0x40f5  -- 40f4 JUMPDEST
    xs 0x40f7 (.push [0x20] (by decide)) ri_push  -- 40f5 PUSH1 0x20
    xs 0x40f8 (.reg .mul) ri_mul  -- 40f7 MUL
    xs 0x40f9 (.reg .add) ri_add  -- 40f8 ADD
    xl 0x40fa 0x360  -- 40f9 MLOAD
    xs 0x40fd (.push [0x03, 0x20] (by decide)) ri_push  -- 40fa PUSH2 0x0320
    xs 0x4100 (.push [0x07, 0x20] (by decide)) ri_push  -- 40fd PUSH2 0x0720
    xl 0x4101 0x720  -- 4100 MLOAD
    xs 0x4103 (.push [0x03] (by decide)) ri_push  -- 4101 PUSH1 0x03
    xs 0x4104 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4103 DUP2
    xs 0x4105 (.reg .lt) ri_lt  -- 4104 LT
    xs 0x4108 (.push [0x41, 0x0d] (by decide)) ri_push  -- 4105 PUSH2 0x410d
    xji 0x4109 0x410d hw
    · xdead
    clear hw
    xjd 0x410e  -- 410d JUMPDEST
    xs 0x4110 (.push [0x20] (by decide)) ri_push  -- 410e PUSH1 0x20
    xs 0x4111 (.reg .mul) ri_mul  -- 4110 MUL
    xs 0x4112 (.reg .add) ri_add  -- 4111 ADD
    xl 0x4113 0x360  -- 4112 MLOAD
    xs 0x4116 (.push [0x05, 0x20] (by decide)) ri_push  -- 4113 PUSH2 0x0520
    xl 0x4117 0x520  -- 4116 MLOAD
    xs 0x4118 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4117 DUP1
    xs 0x4119 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4118 DUP3
    xs 0x411a (.reg .mul) ri_mul  -- 4119 MUL
    xs 0x411b (.reg (.dup 2)) (ri_dup (by rfl))  -- 411a DUP3
    xs 0x411c (.reg .iszero) ri_iszero  -- 411b ISZERO
    xs 0x411d (.reg (.dup 2)) (ri_dup (by rfl))  -- 411c DUP3
    xs 0x411e (.reg (.dup 4)) (ri_dup (by rfl))  -- 411d DUP5
    xs 0x411f (.reg (.dup 3)) (ri_dup (by rfl))  -- 411e DUP4
    xs 0x4120 (.reg .div) ri_div  -- 411f DIV
    xs 0x4121 (.reg .eq) ri_eq  -- 4120 EQ
    xs 0x4122 (.reg .or) ri_or  -- 4121 OR
    xs 0x4125 (.push [0x41, 0x2a] (by decide)) ri_push  -- 4122 PUSH2 0x412a
    xji 0x4126 0x412a hw
    · xdead
    have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x412b  -- 412a JUMPDEST
    xs 0x412c (.reg (.dup 0)) (ri_dup (by rfl))  -- 412b DUP1
    xs 0x412d (.reg (.swap 0)) (ri_swap (by rfl))  -- 412c SWAP1
    xs 0x412e (.reg .pop) ri_pop  -- 412d POP
    xs 0x412f (.reg (.swap 0)) (ri_swap (by rfl))  -- 412e SWAP1
    xs 0x4130 (.reg .pop) ri_pop  -- 412f POP
    xs 0x4131 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4130 SWAP1
    xs 0x4132 (.reg .pop) ri_pop  -- 4131 POP
    xs 0x4135 (.push [0x04, 0x00] (by decide)) ri_push  -- 4132 PUSH2 0x0400
    xl 0x4136 0x400  -- 4135 MLOAD
    xs 0x4137 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4136 DUP1
    xs 0x4138 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4137 DUP1
    xs 0x413b (.push [0x41, 0x40] (by decide)) ri_push  -- 4138 PUSH2 0x4140
    xji 0x413c 0x4140 hw
    · xdead
    have hd0 := hw
    clear hw
    xjd 0x4141  -- 4140 JUMPDEST
    xs 0x4142 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4141 DUP3
    xs 0x4143 (.reg .div) ri_div  -- 4142 DIV
    xs 0x4144 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4143 SWAP1
    xs 0x4145 (.reg .pop) ri_pop  -- 4144 POP
    xs 0x4146 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4145 SWAP1
    xs 0x4147 (.reg .pop) ri_pop  -- 4146 POP
    xs 0x4148 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4147 DUP1
    xs 0x4149 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4148 DUP3
    xs 0x414a (.reg .lt) ri_lt  -- 4149 LT
    xs 0x414b (.reg .iszero) ri_iszero  -- 414a ISZERO
    xs 0x414e (.push [0x41, 0x53] (by decide)) ri_push  -- 414b PUSH2 0x4153
    xji 0x414f 0x4153 hw
    · xdead
    have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0x4154  -- 4153 JUMPDEST
    xs 0x4155 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4154 DUP1
    xs 0x4156 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4155 DUP3
    xs 0x4157 (.reg .sub) ri_sub  -- 4156 SUB
    xs 0x4158 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4157 SWAP1
    xs 0x4159 (.reg .pop) ri_pop  -- 4158 POP
    xs 0x415a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4159 SWAP1
    xs 0x415b (.reg .pop) ri_pop  -- 415a POP
    xs 0x415e (.push [0x07, 0x40] (by decide)) ri_push  -- 415b PUSH2 0x0740
    xsw 0x415f 0x740  -- 415e MSTORE
    xjd 0x4160  -- 415f JUMPDEST
    xs 0x4163 (.push [0x05, 0x40] (by decide)) ri_push  -- 4160 PUSH2 0x0540
    xs 0x4166 (.push [0x07, 0x20] (by decide)) ri_push  -- 4163 PUSH2 0x0720
    xl 0x4167 0x720  -- 4166 MLOAD
    xs 0x4169 (.push [0x03] (by decide)) ri_push  -- 4167 PUSH1 0x03
    xs 0x416a (.reg (.dup 1)) (ri_dup (by rfl))  -- 4169 DUP2
    xs 0x416b (.reg .lt) ri_lt  -- 416a LT
    xs 0x416e (.push [0x41, 0x73] (by decide)) ri_push  -- 416b PUSH2 0x4173
    xji 0x416f 0x4173 hw
    · xdead
    clear hw
    xjd 0x4174  -- 4173 JUMPDEST
    xs 0x4176 (.push [0x20] (by decide)) ri_push  -- 4174 PUSH1 0x20
    xs 0x4177 (.reg .mul) ri_mul  -- 4176 MUL
    xs 0x4178 (.reg .add) ri_add  -- 4177 ADD
    xs 0x4179 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4178 DUP1
    xl 0x417a 0x580  -- 4179 MLOAD
    xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
    xl 0x417e 0x200  -- 417d MLOAD
    xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
    xl 0x4182 0x740  -- 4181 MLOAD
    xs 0x4183 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4182 DUP1
    xs 0x4184 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4183 DUP3
    xs 0x4185 (.reg .mul) ri_mul  -- 4184 MUL
    xs 0x4186 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4185 DUP3
    xs 0x4187 (.reg .iszero) ri_iszero  -- 4186 ISZERO
    xs 0x4188 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4187 DUP3
    xs 0x4189 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4188 DUP5
    xs 0x418a (.reg (.dup 3)) (ri_dup (by rfl))  -- 4189 DUP4
    xs 0x418b (.reg .div) ri_div  -- 418a DIV
    xs 0x418c (.reg .eq) ri_eq  -- 418b EQ
    xs 0x418d (.reg .or) ri_or  -- 418c OR
    xs 0x4190 (.push [0x41, 0x95] (by decide)) ri_push  -- 418d PUSH2 0x4195
    xji 0x4191 0x4195 hw
    · xdead
    have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x4196  -- 4195 JUMPDEST
    xs 0x4197 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4196 DUP1
    xs 0x4198 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4197 SWAP1
    xs 0x4199 (.reg .pop) ri_pop  -- 4198 POP
    xs 0x419a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4199 SWAP1
    xs 0x419b (.reg .pop) ri_pop  -- 419a POP
    xs 0x419c (.reg (.swap 0)) (ri_swap (by rfl))  -- 419b SWAP1
    xs 0x419d (.reg .pop) ri_pop  -- 419c POP
    xs 0x41a3 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 419d PUSH5 0x02540be400
    xs 0x41a4 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a3 DUP1
    xs 0x41a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a4 DUP1
    xs 0x41a8 (.push [0x41, 0xad] (by decide)) ri_push  -- 41a5 PUSH2 0x41ad
    xji 0x41a9 0x41ad hw
    · xdead
    clear hw
    xjd 0x41ae  -- 41ad JUMPDEST
    xs 0x41af (.reg (.dup 2)) (ri_dup (by rfl))  -- 41ae DUP3
    xs 0x41b0 (.reg .div) ri_div  -- 41af DIV
    xs 0x41b1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b0 SWAP1
    xs 0x41b2 (.reg .pop) ri_pop  -- 41b1 POP
    xs 0x41b3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b2 SWAP1
    xs 0x41b4 (.reg .pop) ri_pop  -- 41b3 POP
    xs 0x41b5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41b4 DUP1
    xs 0x41b6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41b5 DUP3
    xs 0x41b7 (.reg .lt) ri_lt  -- 41b6 LT
    xs 0x41b8 (.reg .iszero) ri_iszero  -- 41b7 ISZERO
    xs 0x41bb (.push [0x41, 0xc0] (by decide)) ri_push  -- 41b8 PUSH2 0x41c0
    xji 0x41bc 0x41c0 hw
    · xdead
    have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0x41c1  -- 41c0 JUMPDEST
    xs 0x41c2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41c1 DUP1
    xs 0x41c3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41c2 DUP3
    xs 0x41c4 (.reg .sub) ri_sub  -- 41c3 SUB
    xs 0x41c5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c4 SWAP1
    xs 0x41c6 (.reg .pop) ri_pop  -- 41c5 POP
    xs 0x41c7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c6 SWAP1
    xs 0x41c8 (.reg .pop) ri_pop  -- 41c7 POP
    xs 0x41c9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41c8 DUP2
    xsw 0x41ca 0x580  -- 41c9 MSTORE
    xs 0x41cb (.reg .pop) ri_pop  -- 41ca POP
    xjd 0x41cc  -- 41cb JUMPDEST
    xs 0x41cd (.reg (.dup 1)) (ri_dup (by rfl))  -- 41cc DUP2
    xl 0x41ce 0x720  -- 41cd MLOAD
    xs 0x41d0 (.push [0x01] (by decide)) ri_push  -- 41ce PUSH1 0x01
    xs 0x41d1 (.reg .add) ri_add  -- 41d0 ADD
    xs 0x41d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41d1 DUP1
    xs 0x41d3 (.reg (.dup 3)) (ri_dup (by rfl))  -- 41d2 DUP4
    xsw 0x41d4 0x720  -- 41d3 MSTORE
    xs 0x41d5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41d4 DUP2
    xs 0x41d6 (.reg .eq) ri_eq  -- 41d5 EQ
    xs 0x41d7 (.reg .iszero) ri_iszero  -- 41d6 ISZERO
    xs 0x41da (.push [0x40, 0x5e] (by decide)) ri_push  -- 41d7 PUSH2 0x405e
    xji 0x41db 0x405e hw
    swap
    · exact absurd hw (by decide)
    exact ⟨_, _, _, ⟨hm1, hd0, _, .inr ⟨hne, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
        simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have heq := eqCheck_ne_zero_eq (eqCheck_eq_zero hw)
  clear hw
  xs 0x4076 (.push [0x03, 0x20] (by decide)) ri_push  -- 4073 PUSH2 0x0320
  xs 0x4079 (.push [0x07, 0x20] (by decide)) ri_push  -- 4076 PUSH2 0x0720
  xl 0x407a 0x720  -- 4079 MLOAD
  xs 0x407c (.push [0x03] (by decide)) ri_push  -- 407a PUSH1 0x03
  xs 0x407d (.reg (.dup 1)) (ri_dup (by rfl))  -- 407c DUP2
  xs 0x407e (.reg .lt) ri_lt  -- 407d LT
  xs 0x4081 (.push [0x40, 0x86] (by decide)) ri_push  -- 407e PUSH2 0x4086
  xji 0x4082 0x4086 hw
  · xdead
  clear hw
  xjd 0x4087  -- 4086 JUMPDEST
  xs 0x4089 (.push [0x20] (by decide)) ri_push  -- 4087 PUSH1 0x20
  xs 0x408a (.reg .mul) ri_mul  -- 4089 MUL
  xs 0x408b (.reg .add) ri_add  -- 408a ADD
  xl 0x408c 0x360  -- 408b MLOAD
  xs 0x408f (.push [0x05, 0x20] (by decide)) ri_push  -- 408c PUSH2 0x0520
  xl 0x4090 0x520  -- 408f MLOAD
  xs 0x4091 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4090 DUP1
  xs 0x4092 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4091 DUP3
  xs 0x4093 (.reg .mul) ri_mul  -- 4092 MUL
  xs 0x4094 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4093 DUP3
  xs 0x4095 (.reg .iszero) ri_iszero  -- 4094 ISZERO
  xs 0x4096 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4095 DUP3
  xs 0x4097 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4096 DUP5
  xs 0x4098 (.reg (.dup 3)) (ri_dup (by rfl))  -- 4097 DUP4
  xs 0x4099 (.reg .div) ri_div  -- 4098 DIV
  xs 0x409a (.reg .eq) ri_eq  -- 4099 EQ
  xs 0x409b (.reg .or) ri_or  -- 409a OR
  xs 0x409e (.push [0x40, 0xa3] (by decide)) ri_push  -- 409b PUSH2 0x40a3
  xji 0x409f 0x40a3 hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x40a4  -- 40a3 JUMPDEST
  xs 0x40a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40a4 DUP1
  xs 0x40a6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a5 SWAP1
  xs 0x40a7 (.reg .pop) ri_pop  -- 40a6 POP
  xs 0x40a8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a7 SWAP1
  xs 0x40a9 (.reg .pop) ri_pop  -- 40a8 POP
  xs 0x40aa (.reg (.swap 0)) (ri_swap (by rfl))  -- 40a9 SWAP1
  xs 0x40ab (.reg .pop) ri_pop  -- 40aa POP
  xs 0x40ae (.push [0x04, 0x00] (by decide)) ri_push  -- 40ab PUSH2 0x0400
  xl 0x40af 0x400  -- 40ae MLOAD
  xs 0x40b0 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40af DUP1
  xs 0x40b1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40b0 DUP1
  xs 0x40b4 (.push [0x40, 0xb9] (by decide)) ri_push  -- 40b1 PUSH2 0x40b9
  xji 0x40b5 0x40b9 hw
  · xdead
  have hd0 := hw
  clear hw
  xjd 0x40ba  -- 40b9 JUMPDEST
  xs 0x40bb (.reg (.dup 2)) (ri_dup (by rfl))  -- 40ba DUP3
  xs 0x40bc (.reg .div) ri_div  -- 40bb DIV
  xs 0x40bd (.reg (.swap 0)) (ri_swap (by rfl))  -- 40bc SWAP1
  xs 0x40be (.reg .pop) ri_pop  -- 40bd POP
  xs 0x40bf (.reg (.swap 0)) (ri_swap (by rfl))  -- 40be SWAP1
  xs 0x40c0 (.reg .pop) ri_pop  -- 40bf POP
  xs 0x40c3 (.push [0x05, 0xa0] (by decide)) ri_push  -- 40c0 PUSH2 0x05a0
  xl 0x40c4 0x5a0  -- 40c3 MLOAD
  xs 0x40c5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40c4 DUP1
  xs 0x40c6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 40c5 DUP3
  xs 0x40c7 (.reg .lt) ri_lt  -- 40c6 LT
  xs 0x40c8 (.reg .iszero) ri_iszero  -- 40c7 ISZERO
  xs 0x40cb (.push [0x40, 0xd0] (by decide)) ri_push  -- 40c8 PUSH2 0x40d0
  xji 0x40cc 0x40d0 hw
  · xdead
  have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x40d1  -- 40d0 JUMPDEST
  xs 0x40d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 40d1 DUP1
  xs 0x40d3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 40d2 DUP3
  xs 0x40d4 (.reg .sub) ri_sub  -- 40d3 SUB
  xs 0x40d5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40d4 SWAP1
  xs 0x40d6 (.reg .pop) ri_pop  -- 40d5 POP
  xs 0x40d7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 40d6 SWAP1
  xs 0x40d8 (.reg .pop) ri_pop  -- 40d7 POP
  xs 0x40db (.push [0x07, 0x40] (by decide)) ri_push  -- 40d8 PUSH2 0x0740
  xsw 0x40dc 0x740  -- 40db MSTORE
  xs 0x40df (.push [0x41, 0x5f] (by decide)) ri_push  -- 40dc PUSH2 0x415f
  xjmp 0x415f  -- 40df JUMP
  xjd 0x4160  -- 415f JUMPDEST
  xs 0x4163 (.push [0x05, 0x40] (by decide)) ri_push  -- 4160 PUSH2 0x0540
  xs 0x4166 (.push [0x07, 0x20] (by decide)) ri_push  -- 4163 PUSH2 0x0720
  xl 0x4167 0x720  -- 4166 MLOAD
  xs 0x4169 (.push [0x03] (by decide)) ri_push  -- 4167 PUSH1 0x03
  xs 0x416a (.reg (.dup 1)) (ri_dup (by rfl))  -- 4169 DUP2
  xs 0x416b (.reg .lt) ri_lt  -- 416a LT
  xs 0x416e (.push [0x41, 0x73] (by decide)) ri_push  -- 416b PUSH2 0x4173
  xji 0x416f 0x4173 hw
  · xdead
  clear hw
  xjd 0x4174  -- 4173 JUMPDEST
  xs 0x4176 (.push [0x20] (by decide)) ri_push  -- 4174 PUSH1 0x20
  xs 0x4177 (.reg .mul) ri_mul  -- 4176 MUL
  xs 0x4178 (.reg .add) ri_add  -- 4177 ADD
  xs 0x4179 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4178 DUP1
  xl 0x417a 0x580  -- 4179 MLOAD
  xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
  xl 0x417e 0x200  -- 417d MLOAD
  xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
  xl 0x4182 0x740  -- 4181 MLOAD
  xs 0x4183 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4182 DUP1
  xs 0x4184 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4183 DUP3
  xs 0x4185 (.reg .mul) ri_mul  -- 4184 MUL
  xs 0x4186 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4185 DUP3
  xs 0x4187 (.reg .iszero) ri_iszero  -- 4186 ISZERO
  xs 0x4188 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4187 DUP3
  xs 0x4189 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4188 DUP5
  xs 0x418a (.reg (.dup 3)) (ri_dup (by rfl))  -- 4189 DUP4
  xs 0x418b (.reg .div) ri_div  -- 418a DIV
  xs 0x418c (.reg .eq) ri_eq  -- 418b EQ
  xs 0x418d (.reg .or) ri_or  -- 418c OR
  xs 0x4190 (.push [0x41, 0x95] (by decide)) ri_push  -- 418d PUSH2 0x4195
  xji 0x4191 0x4195 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x4196  -- 4195 JUMPDEST
  xs 0x4197 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4196 DUP1
  xs 0x4198 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4197 SWAP1
  xs 0x4199 (.reg .pop) ri_pop  -- 4198 POP
  xs 0x419a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4199 SWAP1
  xs 0x419b (.reg .pop) ri_pop  -- 419a POP
  xs 0x419c (.reg (.swap 0)) (ri_swap (by rfl))  -- 419b SWAP1
  xs 0x419d (.reg .pop) ri_pop  -- 419c POP
  xs 0x41a3 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 419d PUSH5 0x02540be400
  xs 0x41a4 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a3 DUP1
  xs 0x41a5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41a4 DUP1
  xs 0x41a8 (.push [0x41, 0xad] (by decide)) ri_push  -- 41a5 PUSH2 0x41ad
  xji 0x41a9 0x41ad hw
  · xdead
  clear hw
  xjd 0x41ae  -- 41ad JUMPDEST
  xs 0x41af (.reg (.dup 2)) (ri_dup (by rfl))  -- 41ae DUP3
  xs 0x41b0 (.reg .div) ri_div  -- 41af DIV
  xs 0x41b1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b0 SWAP1
  xs 0x41b2 (.reg .pop) ri_pop  -- 41b1 POP
  xs 0x41b3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41b2 SWAP1
  xs 0x41b4 (.reg .pop) ri_pop  -- 41b3 POP
  xs 0x41b5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41b4 DUP1
  xs 0x41b6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41b5 DUP3
  xs 0x41b7 (.reg .lt) ri_lt  -- 41b6 LT
  xs 0x41b8 (.reg .iszero) ri_iszero  -- 41b7 ISZERO
  xs 0x41bb (.push [0x41, 0xc0] (by decide)) ri_push  -- 41b8 PUSH2 0x41c0
  xji 0x41bc 0x41c0 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x41c1  -- 41c0 JUMPDEST
  xs 0x41c2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41c1 DUP1
  xs 0x41c3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 41c2 DUP3
  xs 0x41c4 (.reg .sub) ri_sub  -- 41c3 SUB
  xs 0x41c5 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c4 SWAP1
  xs 0x41c6 (.reg .pop) ri_pop  -- 41c5 POP
  xs 0x41c7 (.reg (.swap 0)) (ri_swap (by rfl))  -- 41c6 SWAP1
  xs 0x41c8 (.reg .pop) ri_pop  -- 41c7 POP
  xs 0x41c9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41c8 DUP2
  xsw 0x41ca 0x580  -- 41c9 MSTORE
  xs 0x41cb (.reg .pop) ri_pop  -- 41ca POP
  xjd 0x41cc  -- 41cb JUMPDEST
  xs 0x41cd (.reg (.dup 1)) (ri_dup (by rfl))  -- 41cc DUP2
  xl 0x41ce 0x720  -- 41cd MLOAD
  xs 0x41d0 (.push [0x01] (by decide)) ri_push  -- 41ce PUSH1 0x01
  xs 0x41d1 (.reg .add) ri_add  -- 41d0 ADD
  xs 0x41d2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 41d1 DUP1
  xs 0x41d3 (.reg (.dup 3)) (ri_dup (by rfl))  -- 41d2 DUP4
  xsw 0x41d4 0x720  -- 41d3 MSTORE
  xs 0x41d5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41d4 DUP2
  xs 0x41d6 (.reg .eq) ri_eq  -- 41d5 EQ
  xs 0x41d7 (.reg .iszero) ri_iszero  -- 41d6 ISZERO
  xs 0x41da (.push [0x40, 0x5e] (by decide)) ri_push  -- 41d7 PUSH2 0x405e
  xji 0x41db 0x405e hw
  swap
  · exact absurd hw (by decide)
  exact ⟨_, _, _, ⟨hm1, hd0, _, .inl ⟨heq, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩


end

end Blanc.Lift.Curve3Pool
