import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXC
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
  xa 3
  xsw 0x4065 0x740  -- 4064 MSTORE
  xs 0x4068 (.push [0x01, 0x60] (by decide)) ri_push  -- 4065 PUSH2 0x0160
  xl 0x4069 0x160  -- 4068 MLOAD
  xs 0x406c (.push [0x07, 0x20] (by decide)) ri_push  -- 4069 PUSH2 0x0720
  xl 0x406d 0x720  -- 406c MLOAD
  xa 3
  xji 0x4073 0x40e0 hw
  swap
  · have hne := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 3
    xl 0x40e8 0x720  -- 40e7 MLOAD
    xa 4
    xji 0x40f0 0x40f4 hw
    · xdead
    clear hw
    xa 4
    xl 0x40fa 0x320  -- 40f9 MLOAD
    xa 2
    xl 0x4101 0x720  -- 4100 MLOAD
    xa 4
    xji 0x4109 0x410d hw
    · xdead
    clear hw
    xa 4
    xl 0x4113 0x320  -- 4112 MLOAD
    xs 0x4116 (.push [0x05, 0x20] (by decide)) ri_push  -- 4113 PUSH2 0x0520
    xl 0x4117 0x520  -- 4116 MLOAD
    xa 12
    xji 0x4126 0x412a hw
    · xdead
    have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xl 0x4136 0x400  -- 4135 MLOAD
    xa 3
    xji 0x413c 0x4140 hw
    · xdead
    have hd0 := hw
    clear hw
    xa 12
    xji 0x414f 0x4153 hw
    · xdead
    have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0x415f 0x740  -- 415e MSTORE
    xa 3
    xl 0x4167 0x720  -- 4166 MLOAD
    xa 4
    xji 0x416f 0x4173 hw
    · xdead
    clear hw
    xa 5
    xl 0x417a 0x540  -- 4179 MLOAD
    xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
    xl 0x417e 0x200  -- 417d MLOAD
    xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
    xl 0x4182 0x740  -- 4181 MLOAD
    xa 12
    xji 0x4191 0x4195 hw
    · xdead
    have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 12
    xji 0x41a9 0x41ad hw
    · xdead
    clear hw
    xa 12
    xji 0x41bc 0x41c0 hw
    · xdead
    have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0x41ca 0x540  -- 41c9 MSTORE
    xa 3
    xl 0x41ce 0x720  -- 41cd MLOAD
    xa 4
    xsw 0x41d4 0x720  -- 41d3 MSTORE
    xa 4
    xji 0x41db 0x405e hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, ⟨hm1, hd0, _, .inr ⟨hne, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
        simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have heq := B256.eq_of_eqCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
  clear hw
  xa 2
  xl 0x407a 0x720  -- 4079 MLOAD
  xa 4
  xji 0x4082 0x4086 hw
  · xdead
  clear hw
  xa 4
  xl 0x408c 0x320  -- 408b MLOAD
  xs 0x408f (.push [0x05, 0x20] (by decide)) ri_push  -- 408c PUSH2 0x0520
  xl 0x4090 0x520  -- 408f MLOAD
  xa 12
  xji 0x409f 0x40a3 hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x40af 0x400  -- 40ae MLOAD
  xa 3
  xji 0x40b5 0x40b9 hw
  · xdead
  have hd0 := hw
  clear hw
  xa 8
  xl 0x40c4 0x5a0  -- 40c3 MLOAD
  xa 5
  xji 0x40cc 0x40d0 hw
  · xdead
  have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x40dc 0x740  -- 40db MSTORE
  xs 0x40df (.push [0x41, 0x5f] (by decide)) ri_push  -- 40dc PUSH2 0x415f
  xjmp 0x415f  -- 40df JUMP
  xa 3
  xl 0x4167 0x720  -- 4166 MLOAD
  xa 4
  xji 0x416f 0x4173 hw
  · xdead
  clear hw
  xa 5
  xl 0x417a 0x540  -- 4179 MLOAD
  xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
  xl 0x417e 0x200  -- 417d MLOAD
  xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
  xl 0x4182 0x740  -- 4181 MLOAD
  xa 12
  xji 0x4191 0x4195 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x41a9 0x41ad hw
  · xdead
  clear hw
  xa 12
  xji 0x41bc 0x41c0 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x41ca 0x540  -- 41c9 MSTORE
  xa 3
  xl 0x41ce 0x720  -- 41cd MLOAD
  xa 4
  xsw 0x41d4 0x720  -- 41d3 MSTORE
  xa 4
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
  xa 3
  xsw 0x4065 0x740  -- 4064 MSTORE
  xs 0x4068 (.push [0x01, 0x60] (by decide)) ri_push  -- 4065 PUSH2 0x0160
  xl 0x4069 0x160  -- 4068 MLOAD
  xs 0x406c (.push [0x07, 0x20] (by decide)) ri_push  -- 4069 PUSH2 0x0720
  xl 0x406d 0x720  -- 406c MLOAD
  xa 3
  xji 0x4073 0x40e0 hw
  swap
  · have hne := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 3
    xl 0x40e8 0x720  -- 40e7 MLOAD
    xa 4
    xji 0x40f0 0x40f4 hw
    · xdead
    clear hw
    xa 4
    xl 0x40fa 0x340  -- 40f9 MLOAD
    xa 2
    xl 0x4101 0x720  -- 4100 MLOAD
    xa 4
    xji 0x4109 0x410d hw
    · xdead
    clear hw
    xa 4
    xl 0x4113 0x340  -- 4112 MLOAD
    xs 0x4116 (.push [0x05, 0x20] (by decide)) ri_push  -- 4113 PUSH2 0x0520
    xl 0x4117 0x520  -- 4116 MLOAD
    xa 12
    xji 0x4126 0x412a hw
    · xdead
    have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xl 0x4136 0x400  -- 4135 MLOAD
    xa 3
    xji 0x413c 0x4140 hw
    · xdead
    have hd0 := hw
    clear hw
    xa 12
    xji 0x414f 0x4153 hw
    · xdead
    have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0x415f 0x740  -- 415e MSTORE
    xa 3
    xl 0x4167 0x720  -- 4166 MLOAD
    xa 4
    xji 0x416f 0x4173 hw
    · xdead
    clear hw
    xa 5
    xl 0x417a 0x560  -- 4179 MLOAD
    xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
    xl 0x417e 0x200  -- 417d MLOAD
    xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
    xl 0x4182 0x740  -- 4181 MLOAD
    xa 12
    xji 0x4191 0x4195 hw
    · xdead
    have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 12
    xji 0x41a9 0x41ad hw
    · xdead
    clear hw
    xa 12
    xji 0x41bc 0x41c0 hw
    · xdead
    have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0x41ca 0x560  -- 41c9 MSTORE
    xa 3
    xl 0x41ce 0x720  -- 41cd MLOAD
    xa 4
    xsw 0x41d4 0x720  -- 41d3 MSTORE
    xa 4
    xji 0x41db 0x405e hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, ⟨hm1, hd0, _, .inr ⟨hne, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
        simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have heq := B256.eq_of_eqCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
  clear hw
  xa 2
  xl 0x407a 0x720  -- 4079 MLOAD
  xa 4
  xji 0x4082 0x4086 hw
  · xdead
  clear hw
  xa 4
  xl 0x408c 0x340  -- 408b MLOAD
  xs 0x408f (.push [0x05, 0x20] (by decide)) ri_push  -- 408c PUSH2 0x0520
  xl 0x4090 0x520  -- 408f MLOAD
  xa 12
  xji 0x409f 0x40a3 hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x40af 0x400  -- 40ae MLOAD
  xa 3
  xji 0x40b5 0x40b9 hw
  · xdead
  have hd0 := hw
  clear hw
  xa 8
  xl 0x40c4 0x5a0  -- 40c3 MLOAD
  xa 5
  xji 0x40cc 0x40d0 hw
  · xdead
  have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x40dc 0x740  -- 40db MSTORE
  xs 0x40df (.push [0x41, 0x5f] (by decide)) ri_push  -- 40dc PUSH2 0x415f
  xjmp 0x415f  -- 40df JUMP
  xa 3
  xl 0x4167 0x720  -- 4166 MLOAD
  xa 4
  xji 0x416f 0x4173 hw
  · xdead
  clear hw
  xa 5
  xl 0x417a 0x560  -- 4179 MLOAD
  xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
  xl 0x417e 0x200  -- 417d MLOAD
  xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
  xl 0x4182 0x740  -- 4181 MLOAD
  xa 12
  xji 0x4191 0x4195 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x41a9 0x41ad hw
  · xdead
  clear hw
  xa 12
  xji 0x41bc 0x41c0 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x41ca 0x560  -- 41c9 MSTORE
  xa 3
  xl 0x41ce 0x720  -- 41cd MLOAD
  xa 4
  xsw 0x41d4 0x720  -- 41d3 MSTORE
  xa 4
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
  xa 3
  xsw 0x4065 0x740  -- 4064 MSTORE
  xs 0x4068 (.push [0x01, 0x60] (by decide)) ri_push  -- 4065 PUSH2 0x0160
  xl 0x4069 0x160  -- 4068 MLOAD
  xs 0x406c (.push [0x07, 0x20] (by decide)) ri_push  -- 4069 PUSH2 0x0720
  xl 0x406d 0x720  -- 406c MLOAD
  xa 3
  xji 0x4073 0x40e0 hw
  swap
  · have hne := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 3
    xl 0x40e8 0x720  -- 40e7 MLOAD
    xa 4
    xji 0x40f0 0x40f4 hw
    · xdead
    clear hw
    xa 4
    xl 0x40fa 0x360  -- 40f9 MLOAD
    xa 2
    xl 0x4101 0x720  -- 4100 MLOAD
    xa 4
    xji 0x4109 0x410d hw
    · xdead
    clear hw
    xa 4
    xl 0x4113 0x360  -- 4112 MLOAD
    xs 0x4116 (.push [0x05, 0x20] (by decide)) ri_push  -- 4113 PUSH2 0x0520
    xl 0x4117 0x520  -- 4116 MLOAD
    xa 12
    xji 0x4126 0x412a hw
    · xdead
    have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xl 0x4136 0x400  -- 4135 MLOAD
    xa 3
    xji 0x413c 0x4140 hw
    · xdead
    have hd0 := hw
    clear hw
    xa 12
    xji 0x414f 0x4153 hw
    · xdead
    have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0x415f 0x740  -- 415e MSTORE
    xa 3
    xl 0x4167 0x720  -- 4166 MLOAD
    xa 4
    xji 0x416f 0x4173 hw
    · xdead
    clear hw
    xa 5
    xl 0x417a 0x580  -- 4179 MLOAD
    xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
    xl 0x417e 0x200  -- 417d MLOAD
    xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
    xl 0x4182 0x740  -- 4181 MLOAD
    xa 12
    xji 0x4191 0x4195 hw
    · xdead
    have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xa 12
    xji 0x41a9 0x41ad hw
    · xdead
    clear hw
    xa 12
    xji 0x41bc 0x41c0 hw
    · xdead
    have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0x41ca 0x580  -- 41c9 MSTORE
    xa 3
    xl 0x41ce 0x720  -- 41cd MLOAD
    xa 4
    xsw 0x41d4 0x720  -- 41d3 MSTORE
    xa 4
    xji 0x41db 0x405e hw
    swap
    · exact absurd hw (by decide)
    exact ⟨_, _, _, ⟨hm1, hd0, _, .inr ⟨hne, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
        simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have heq := B256.eq_of_eqCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
  clear hw
  xa 2
  xl 0x407a 0x720  -- 4079 MLOAD
  xa 4
  xji 0x4082 0x4086 hw
  · xdead
  clear hw
  xa 4
  xl 0x408c 0x360  -- 408b MLOAD
  xs 0x408f (.push [0x05, 0x20] (by decide)) ri_push  -- 408c PUSH2 0x0520
  xl 0x4090 0x520  -- 408f MLOAD
  xa 12
  xji 0x409f 0x40a3 hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x40af 0x400  -- 40ae MLOAD
  xa 3
  xji 0x40b5 0x40b9 hw
  · xdead
  have hd0 := hw
  clear hw
  xa 8
  xl 0x40c4 0x5a0  -- 40c3 MLOAD
  xa 5
  xji 0x40cc 0x40d0 hw
  · xdead
  have hs := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x40dc 0x740  -- 40db MSTORE
  xs 0x40df (.push [0x41, 0x5f] (by decide)) ri_push  -- 40dc PUSH2 0x415f
  xjmp 0x415f  -- 40df JUMP
  xa 3
  xl 0x4167 0x720  -- 4166 MLOAD
  xa 4
  xji 0x416f 0x4173 hw
  · xdead
  clear hw
  xa 5
  xl 0x417a 0x580  -- 4179 MLOAD
  xs 0x417d (.push [0x02, 0x00] (by decide)) ri_push  -- 417a PUSH2 0x0200
  xl 0x417e 0x200  -- 417d MLOAD
  xs 0x4181 (.push [0x07, 0x40] (by decide)) ri_push  -- 417e PUSH2 0x0740
  xl 0x4182 0x740  -- 4181 MLOAD
  xa 12
  xji 0x4191 0x4195 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x41a9 0x41ad hw
  · xdead
  clear hw
  xa 12
  xji 0x41bc 0x41c0 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x41ca 0x580  -- 41c9 MSTORE
  xa 3
  xl 0x41ce 0x720  -- 41cd MLOAD
  xa 4
  xsw 0x41d4 0x720  -- 41d3 MSTORE
  xa 4
  xji 0x41db 0x405e hw
  swap
  · exact absurd hw (by decide)
  exact ⟨_, _, _, ⟨hm1, hd0, _, .inl ⟨heq, hs, rfl⟩, hm2, hs2, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩


end

end Blanc.Lift.Curve3Pool
