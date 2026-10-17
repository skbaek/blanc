import Blanc.Lift.Curve3Pool.Walk.ViewsCta

/-!
# `calc_token_amount`'s balance loop (`0xc1f`), unrolled

Each iteration `k` reads the counter at `0x320`, then `balances[k] ± amounts[k]` (checked) by
the `deposit` flag at `0x64`, written back to `0x140 + 32k`; the counter is bumped.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The `deposit` word and the `k`-th amount word as the loop reads them. -/
abbrev ctaDep (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [100])
abbrev ctaAmt (sevm : Sevm) (k : UInt8) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [32] * Bytes.toB256 [k] + Bytes.toB256 [4])

/-- One step's checked update of a balance word by the deposit flag. -/
def CtaUpd (dep B a v : B256) : Prop :=
  (dep ≠ 0 ∧ B.toNat + a.toNat < 2 ^ 256 ∧ v = B + a) ∨ (dep = 0 ∧ a.toNat ≤ B.toNat ∧ v = B - a)

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}


/-- **Iteration 0** of the balance loop. -/
theorem xa_cta_it0 {M : Mem} {D0 amp B0 B1 B2 ck : B256}
    (hcode : sevm.code = code) (hck : ck = Bytes.toB256 [0])
    (hV : VW M [(0x320, ck), (0x200, D0), (0x140, B0), (0x160, B1), (0x180, B2), (0x1a0, amp)])
    (h : XAt sevm post 0xc1f (St b [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [3, 32]] M G) L) :
    ∃ v M' G', CtaUpd (ctaDep sevm) B0 (ctaAmt sevm 0) v ∧
      XAt sevm post 0xc1f (St b [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [3, 32]] M' G') L ∧
      VW M' [(0x320, Bytes.toB256 [1] + Bytes.toB256 [0]), (0x200, D0), (0x140, v), (0x160, B1), (0x180, B2),
        (0x1a0, amp)] := by
  subst hck
  xjd 0xc20  -- c1f JUMPDEST
  xs 0xc22 (.push [0x64] (by decide)) ri_push  -- c20 PUSH1 0x64
  xs 0xc23 (.reg .calldataload) ri_calldataload  -- c22 CALLDATALOAD
  xs 0xc24 (.reg .iszero) ri_iszero  -- c23 ISZERO
  xs 0xc27 (.push [0x0c, 0x77] (by decide)) ri_push  -- c24 PUSH2 0x0c77
  xji 0xc28 0xc77 hw
  swap
  · have hd0 := eqCheck_ne_zero_eq hw
    clear hw
    xjd 0xc78  -- c77 JUMPDEST
    xs 0xc7b (.push [0x01, 0x40] (by decide)) ri_push  -- c78 PUSH2 0x0140
    xs 0xc7e (.push [0x03, 0x20] (by decide)) ri_push  -- c7b PUSH2 0x0320
    xl 0xc7f 0x320  -- c7e MLOAD
    xs 0xc81 (.push [0x03] (by decide)) ri_push  -- c7f PUSH1 0x03
    xs 0xc82 (.reg (.dup 1)) (ri_dup (by rfl))  -- c81 DUP2
    xs 0xc83 (.reg .lt) ri_lt  -- c82 LT
    xs 0xc86 (.push [0x0c, 0x8b] (by decide)) ri_push  -- c83 PUSH2 0x0c8b
    xji 0xc87 0xc8b hw
    · xdead
    clear hw
    xjd 0xc8c  -- c8b JUMPDEST
    xs 0xc8e (.push [0x20] (by decide)) ri_push  -- c8c PUSH1 0x20
    xs 0xc8f (.reg .mul) ri_mul  -- c8e MUL
    xs 0xc90 (.reg .add) ri_add  -- c8f ADD
    xs 0xc91 (.reg (.dup 0)) (ri_dup (by rfl))  -- c90 DUP1
    xl 0xc92 0x140  -- c91 MLOAD
    xs 0xc94 (.push [0x04] (by decide)) ri_push  -- c92 PUSH1 0x04
    xs 0xc97 (.push [0x03, 0x20] (by decide)) ri_push  -- c94 PUSH2 0x0320
    xl 0xc98 0x320  -- c97 MLOAD
    xs 0xc9a (.push [0x03] (by decide)) ri_push  -- c98 PUSH1 0x03
    xs 0xc9b (.reg (.dup 1)) (ri_dup (by rfl))  -- c9a DUP2
    xs 0xc9c (.reg .lt) ri_lt  -- c9b LT
    xs 0xc9f (.push [0x0c, 0xa4] (by decide)) ri_push  -- c9c PUSH2 0x0ca4
    xji 0xca0 0xca4 hw
    · xdead
    clear hw
    xjd 0xca5  -- ca4 JUMPDEST
    xs 0xca7 (.push [0x20] (by decide)) ri_push  -- ca5 PUSH1 0x20
    xs 0xca8 (.reg .mul) ri_mul  -- ca7 MUL
    xs 0xca9 (.reg .add) ri_add  -- ca8 ADD
    xs 0xcaa (.reg .calldataload) ri_calldataload  -- ca9 CALLDATALOAD
    xs 0xcab (.reg (.dup 0)) (ri_dup (by rfl))  -- caa DUP1
    xs 0xcac (.reg (.dup 2)) (ri_dup (by rfl))  -- cab DUP3
    xs 0xcad (.reg .lt) ri_lt  -- cac LT
    xs 0xcae (.reg .iszero) ri_iszero  -- cad ISZERO
    xs 0xcb1 (.push [0x0c, 0xb6] (by decide)) ri_push  -- cae PUSH2 0x0cb6
    xji 0xcb2 0xcb6 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0xcb7  -- cb6 JUMPDEST
    xs 0xcb8 (.reg (.dup 0)) (ri_dup (by rfl))  -- cb7 DUP1
    xs 0xcb9 (.reg (.dup 2)) (ri_dup (by rfl))  -- cb8 DUP3
    xs 0xcba (.reg .sub) ri_sub  -- cb9 SUB
    xs 0xcbb (.reg (.swap 0)) (ri_swap (by rfl))  -- cba SWAP1
    xs 0xcbc (.reg .pop) ri_pop  -- cbb POP
    xs 0xcbd (.reg (.swap 0)) (ri_swap (by rfl))  -- cbc SWAP1
    xs 0xcbe (.reg .pop) ri_pop  -- cbd POP
    xs 0xcbf (.reg (.dup 1)) (ri_dup (by rfl))  -- cbe DUP2
    xsw 0xcc0 0x140  -- cbf MSTORE
    xs 0xcc1 (.reg .pop) ri_pop  -- cc0 POP
    xjd 0xcc2  -- cc1 JUMPDEST
    xjd 0xcc3  -- cc2 JUMPDEST
    xs 0xcc4 (.reg (.dup 1)) (ri_dup (by rfl))  -- cc3 DUP2
    xl 0xcc5 0x320  -- cc4 MLOAD
    xs 0xcc7 (.push [0x01] (by decide)) ri_push  -- cc5 PUSH1 0x01
    xs 0xcc8 (.reg .add) ri_add  -- cc7 ADD
    xs 0xcc9 (.reg (.dup 0)) (ri_dup (by rfl))  -- cc8 DUP1
    xs 0xcca (.reg (.dup 3)) (ri_dup (by rfl))  -- cc9 DUP4
    xsw 0xccb 0x320  -- cca MSTORE
    xs 0xccc (.reg (.dup 1)) (ri_dup (by rfl))  -- ccb DUP2
    xs 0xccd (.reg .eq) ri_eq  -- ccc EQ
    xs 0xcce (.reg .iszero) ri_iszero  -- ccd ISZERO
    xs 0xcd1 (.push [0x0c, 0x1f] (by decide)) ri_push  -- cce PUSH2 0x0c1f
    xji 0xcd2 0xc1f hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, .inr ⟨hd0, hle, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have hd1 := eqCheck_eq_zero hw
  clear hw
  xs 0xc2b (.push [0x01, 0x40] (by decide)) ri_push  -- c28 PUSH2 0x0140
  xs 0xc2e (.push [0x03, 0x20] (by decide)) ri_push  -- c2b PUSH2 0x0320
  xl 0xc2f 0x320  -- c2e MLOAD
  xs 0xc31 (.push [0x03] (by decide)) ri_push  -- c2f PUSH1 0x03
  xs 0xc32 (.reg (.dup 1)) (ri_dup (by rfl))  -- c31 DUP2
  xs 0xc33 (.reg .lt) ri_lt  -- c32 LT
  xs 0xc36 (.push [0x0c, 0x3b] (by decide)) ri_push  -- c33 PUSH2 0x0c3b
  xji 0xc37 0xc3b hw
  · xdead
  clear hw
  xjd 0xc3c  -- c3b JUMPDEST
  xs 0xc3e (.push [0x20] (by decide)) ri_push  -- c3c PUSH1 0x20
  xs 0xc3f (.reg .mul) ri_mul  -- c3e MUL
  xs 0xc40 (.reg .add) ri_add  -- c3f ADD
  xs 0xc41 (.reg (.dup 0)) (ri_dup (by rfl))  -- c40 DUP1
  xl 0xc42 0x140  -- c41 MLOAD
  xs 0xc44 (.push [0x04] (by decide)) ri_push  -- c42 PUSH1 0x04
  xs 0xc47 (.push [0x03, 0x20] (by decide)) ri_push  -- c44 PUSH2 0x0320
  xl 0xc48 0x320  -- c47 MLOAD
  xs 0xc4a (.push [0x03] (by decide)) ri_push  -- c48 PUSH1 0x03
  xs 0xc4b (.reg (.dup 1)) (ri_dup (by rfl))  -- c4a DUP2
  xs 0xc4c (.reg .lt) ri_lt  -- c4b LT
  xs 0xc4f (.push [0x0c, 0x54] (by decide)) ri_push  -- c4c PUSH2 0x0c54
  xji 0xc50 0xc54 hw
  · xdead
  clear hw
  xjd 0xc55  -- c54 JUMPDEST
  xs 0xc57 (.push [0x20] (by decide)) ri_push  -- c55 PUSH1 0x20
  xs 0xc58 (.reg .mul) ri_mul  -- c57 MUL
  xs 0xc59 (.reg .add) ri_add  -- c58 ADD
  xs 0xc5a (.reg .calldataload) ri_calldataload  -- c59 CALLDATALOAD
  xs 0xc5b (.reg (.dup 1)) (ri_dup (by rfl))  -- c5a DUP2
  xs 0xc5c (.reg (.dup 1)) (ri_dup (by rfl))  -- c5b DUP2
  xs 0xc5d (.reg (.dup 3)) (ri_dup (by rfl))  -- c5c DUP4
  xs 0xc5e (.reg .add) ri_add  -- c5d ADD
  xs 0xc5f (.reg .lt) ri_lt  -- c5e LT
  xs 0xc60 (.reg .iszero) ri_iszero  -- c5f ISZERO
  xs 0xc63 (.push [0x0c, 0x68] (by decide)) ri_push  -- c60 PUSH2 0x0c68
  xji 0xc64 0xc68 hw
  · xdead
  have hadd := (B256.nof_iff_not_add_lt _ _).mpr
    (ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xjd 0xc69  -- c68 JUMPDEST
  xs 0xc6a (.reg (.dup 0)) (ri_dup (by rfl))  -- c69 DUP1
  xs 0xc6b (.reg (.dup 2)) (ri_dup (by rfl))  -- c6a DUP3
  xs 0xc6c (.reg .add) ri_add  -- c6b ADD
  xs 0xc6d (.reg (.swap 0)) (ri_swap (by rfl))  -- c6c SWAP1
  xs 0xc6e (.reg .pop) ri_pop  -- c6d POP
  xs 0xc6f (.reg (.swap 0)) (ri_swap (by rfl))  -- c6e SWAP1
  xs 0xc70 (.reg .pop) ri_pop  -- c6f POP
  xs 0xc71 (.reg (.dup 1)) (ri_dup (by rfl))  -- c70 DUP2
  xsw 0xc72 0x140  -- c71 MSTORE
  xs 0xc73 (.reg .pop) ri_pop  -- c72 POP
  xs 0xc76 (.push [0x0c, 0xc1] (by decide)) ri_push  -- c73 PUSH2 0x0cc1
  xjmp 0xcc1  -- c76 JUMP
  xjd 0xcc2  -- cc1 JUMPDEST
  xjd 0xcc3  -- cc2 JUMPDEST
  xs 0xcc4 (.reg (.dup 1)) (ri_dup (by rfl))  -- cc3 DUP2
  xl 0xcc5 0x320  -- cc4 MLOAD
  xs 0xcc7 (.push [0x01] (by decide)) ri_push  -- cc5 PUSH1 0x01
  xs 0xcc8 (.reg .add) ri_add  -- cc7 ADD
  xs 0xcc9 (.reg (.dup 0)) (ri_dup (by rfl))  -- cc8 DUP1
  xs 0xcca (.reg (.dup 3)) (ri_dup (by rfl))  -- cc9 DUP4
  xsw 0xccb 0x320  -- cca MSTORE
  xs 0xccc (.reg (.dup 1)) (ri_dup (by rfl))  -- ccb DUP2
  xs 0xccd (.reg .eq) ri_eq  -- ccc EQ
  xs 0xcce (.reg .iszero) ri_iszero  -- ccd ISZERO
  xs 0xcd1 (.push [0x0c, 0x1f] (by decide)) ri_push  -- cce PUSH2 0x0c1f
  xji 0xcd2 0xc1f hw
  · exact absurd hw (by decide)
  exact ⟨_, _, _, .inl ⟨hd1, hadd, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩


/-- **Iteration 1** of the balance loop. -/
theorem xa_cta_it1 {M : Mem} {D0 amp B0 B1 B2 ck : B256}
    (hcode : sevm.code = code) (hck : ck = Bytes.toB256 [1])
    (hV : VW M [(0x320, ck), (0x200, D0), (0x140, B0), (0x160, B1), (0x180, B2), (0x1a0, amp)])
    (h : XAt sevm post 0xc1f (St b [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [3, 32]] M G) L) :
    ∃ v M' G', CtaUpd (ctaDep sevm) B1 (ctaAmt sevm 1) v ∧
      XAt sevm post 0xc1f (St b [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [3, 32]] M' G') L ∧
      VW M' [(0x320, Bytes.toB256 [1] + Bytes.toB256 [1]), (0x200, D0), (0x140, B0), (0x160, v), (0x180, B2),
        (0x1a0, amp)] := by
  subst hck
  xjd 0xc20  -- c1f JUMPDEST
  xs 0xc22 (.push [0x64] (by decide)) ri_push  -- c20 PUSH1 0x64
  xs 0xc23 (.reg .calldataload) ri_calldataload  -- c22 CALLDATALOAD
  xs 0xc24 (.reg .iszero) ri_iszero  -- c23 ISZERO
  xs 0xc27 (.push [0x0c, 0x77] (by decide)) ri_push  -- c24 PUSH2 0x0c77
  xji 0xc28 0xc77 hw
  swap
  · have hd0 := eqCheck_ne_zero_eq hw
    clear hw
    xjd 0xc78  -- c77 JUMPDEST
    xs 0xc7b (.push [0x01, 0x40] (by decide)) ri_push  -- c78 PUSH2 0x0140
    xs 0xc7e (.push [0x03, 0x20] (by decide)) ri_push  -- c7b PUSH2 0x0320
    xl 0xc7f 0x320  -- c7e MLOAD
    xs 0xc81 (.push [0x03] (by decide)) ri_push  -- c7f PUSH1 0x03
    xs 0xc82 (.reg (.dup 1)) (ri_dup (by rfl))  -- c81 DUP2
    xs 0xc83 (.reg .lt) ri_lt  -- c82 LT
    xs 0xc86 (.push [0x0c, 0x8b] (by decide)) ri_push  -- c83 PUSH2 0x0c8b
    xji 0xc87 0xc8b hw
    · xdead
    clear hw
    xjd 0xc8c  -- c8b JUMPDEST
    xs 0xc8e (.push [0x20] (by decide)) ri_push  -- c8c PUSH1 0x20
    xs 0xc8f (.reg .mul) ri_mul  -- c8e MUL
    xs 0xc90 (.reg .add) ri_add  -- c8f ADD
    xs 0xc91 (.reg (.dup 0)) (ri_dup (by rfl))  -- c90 DUP1
    xl 0xc92 0x160  -- c91 MLOAD
    xs 0xc94 (.push [0x04] (by decide)) ri_push  -- c92 PUSH1 0x04
    xs 0xc97 (.push [0x03, 0x20] (by decide)) ri_push  -- c94 PUSH2 0x0320
    xl 0xc98 0x320  -- c97 MLOAD
    xs 0xc9a (.push [0x03] (by decide)) ri_push  -- c98 PUSH1 0x03
    xs 0xc9b (.reg (.dup 1)) (ri_dup (by rfl))  -- c9a DUP2
    xs 0xc9c (.reg .lt) ri_lt  -- c9b LT
    xs 0xc9f (.push [0x0c, 0xa4] (by decide)) ri_push  -- c9c PUSH2 0x0ca4
    xji 0xca0 0xca4 hw
    · xdead
    clear hw
    xjd 0xca5  -- ca4 JUMPDEST
    xs 0xca7 (.push [0x20] (by decide)) ri_push  -- ca5 PUSH1 0x20
    xs 0xca8 (.reg .mul) ri_mul  -- ca7 MUL
    xs 0xca9 (.reg .add) ri_add  -- ca8 ADD
    xs 0xcaa (.reg .calldataload) ri_calldataload  -- ca9 CALLDATALOAD
    xs 0xcab (.reg (.dup 0)) (ri_dup (by rfl))  -- caa DUP1
    xs 0xcac (.reg (.dup 2)) (ri_dup (by rfl))  -- cab DUP3
    xs 0xcad (.reg .lt) ri_lt  -- cac LT
    xs 0xcae (.reg .iszero) ri_iszero  -- cad ISZERO
    xs 0xcb1 (.push [0x0c, 0xb6] (by decide)) ri_push  -- cae PUSH2 0x0cb6
    xji 0xcb2 0xcb6 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0xcb7  -- cb6 JUMPDEST
    xs 0xcb8 (.reg (.dup 0)) (ri_dup (by rfl))  -- cb7 DUP1
    xs 0xcb9 (.reg (.dup 2)) (ri_dup (by rfl))  -- cb8 DUP3
    xs 0xcba (.reg .sub) ri_sub  -- cb9 SUB
    xs 0xcbb (.reg (.swap 0)) (ri_swap (by rfl))  -- cba SWAP1
    xs 0xcbc (.reg .pop) ri_pop  -- cbb POP
    xs 0xcbd (.reg (.swap 0)) (ri_swap (by rfl))  -- cbc SWAP1
    xs 0xcbe (.reg .pop) ri_pop  -- cbd POP
    xs 0xcbf (.reg (.dup 1)) (ri_dup (by rfl))  -- cbe DUP2
    xsw 0xcc0 0x160  -- cbf MSTORE
    xs 0xcc1 (.reg .pop) ri_pop  -- cc0 POP
    xjd 0xcc2  -- cc1 JUMPDEST
    xjd 0xcc3  -- cc2 JUMPDEST
    xs 0xcc4 (.reg (.dup 1)) (ri_dup (by rfl))  -- cc3 DUP2
    xl 0xcc5 0x320  -- cc4 MLOAD
    xs 0xcc7 (.push [0x01] (by decide)) ri_push  -- cc5 PUSH1 0x01
    xs 0xcc8 (.reg .add) ri_add  -- cc7 ADD
    xs 0xcc9 (.reg (.dup 0)) (ri_dup (by rfl))  -- cc8 DUP1
    xs 0xcca (.reg (.dup 3)) (ri_dup (by rfl))  -- cc9 DUP4
    xsw 0xccb 0x320  -- cca MSTORE
    xs 0xccc (.reg (.dup 1)) (ri_dup (by rfl))  -- ccb DUP2
    xs 0xccd (.reg .eq) ri_eq  -- ccc EQ
    xs 0xcce (.reg .iszero) ri_iszero  -- ccd ISZERO
    xs 0xcd1 (.push [0x0c, 0x1f] (by decide)) ri_push  -- cce PUSH2 0x0c1f
    xji 0xcd2 0xc1f hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, .inr ⟨hd0, hle, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have hd1 := eqCheck_eq_zero hw
  clear hw
  xs 0xc2b (.push [0x01, 0x40] (by decide)) ri_push  -- c28 PUSH2 0x0140
  xs 0xc2e (.push [0x03, 0x20] (by decide)) ri_push  -- c2b PUSH2 0x0320
  xl 0xc2f 0x320  -- c2e MLOAD
  xs 0xc31 (.push [0x03] (by decide)) ri_push  -- c2f PUSH1 0x03
  xs 0xc32 (.reg (.dup 1)) (ri_dup (by rfl))  -- c31 DUP2
  xs 0xc33 (.reg .lt) ri_lt  -- c32 LT
  xs 0xc36 (.push [0x0c, 0x3b] (by decide)) ri_push  -- c33 PUSH2 0x0c3b
  xji 0xc37 0xc3b hw
  · xdead
  clear hw
  xjd 0xc3c  -- c3b JUMPDEST
  xs 0xc3e (.push [0x20] (by decide)) ri_push  -- c3c PUSH1 0x20
  xs 0xc3f (.reg .mul) ri_mul  -- c3e MUL
  xs 0xc40 (.reg .add) ri_add  -- c3f ADD
  xs 0xc41 (.reg (.dup 0)) (ri_dup (by rfl))  -- c40 DUP1
  xl 0xc42 0x160  -- c41 MLOAD
  xs 0xc44 (.push [0x04] (by decide)) ri_push  -- c42 PUSH1 0x04
  xs 0xc47 (.push [0x03, 0x20] (by decide)) ri_push  -- c44 PUSH2 0x0320
  xl 0xc48 0x320  -- c47 MLOAD
  xs 0xc4a (.push [0x03] (by decide)) ri_push  -- c48 PUSH1 0x03
  xs 0xc4b (.reg (.dup 1)) (ri_dup (by rfl))  -- c4a DUP2
  xs 0xc4c (.reg .lt) ri_lt  -- c4b LT
  xs 0xc4f (.push [0x0c, 0x54] (by decide)) ri_push  -- c4c PUSH2 0x0c54
  xji 0xc50 0xc54 hw
  · xdead
  clear hw
  xjd 0xc55  -- c54 JUMPDEST
  xs 0xc57 (.push [0x20] (by decide)) ri_push  -- c55 PUSH1 0x20
  xs 0xc58 (.reg .mul) ri_mul  -- c57 MUL
  xs 0xc59 (.reg .add) ri_add  -- c58 ADD
  xs 0xc5a (.reg .calldataload) ri_calldataload  -- c59 CALLDATALOAD
  xs 0xc5b (.reg (.dup 1)) (ri_dup (by rfl))  -- c5a DUP2
  xs 0xc5c (.reg (.dup 1)) (ri_dup (by rfl))  -- c5b DUP2
  xs 0xc5d (.reg (.dup 3)) (ri_dup (by rfl))  -- c5c DUP4
  xs 0xc5e (.reg .add) ri_add  -- c5d ADD
  xs 0xc5f (.reg .lt) ri_lt  -- c5e LT
  xs 0xc60 (.reg .iszero) ri_iszero  -- c5f ISZERO
  xs 0xc63 (.push [0x0c, 0x68] (by decide)) ri_push  -- c60 PUSH2 0x0c68
  xji 0xc64 0xc68 hw
  · xdead
  have hadd := (B256.nof_iff_not_add_lt _ _).mpr
    (ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xjd 0xc69  -- c68 JUMPDEST
  xs 0xc6a (.reg (.dup 0)) (ri_dup (by rfl))  -- c69 DUP1
  xs 0xc6b (.reg (.dup 2)) (ri_dup (by rfl))  -- c6a DUP3
  xs 0xc6c (.reg .add) ri_add  -- c6b ADD
  xs 0xc6d (.reg (.swap 0)) (ri_swap (by rfl))  -- c6c SWAP1
  xs 0xc6e (.reg .pop) ri_pop  -- c6d POP
  xs 0xc6f (.reg (.swap 0)) (ri_swap (by rfl))  -- c6e SWAP1
  xs 0xc70 (.reg .pop) ri_pop  -- c6f POP
  xs 0xc71 (.reg (.dup 1)) (ri_dup (by rfl))  -- c70 DUP2
  xsw 0xc72 0x160  -- c71 MSTORE
  xs 0xc73 (.reg .pop) ri_pop  -- c72 POP
  xs 0xc76 (.push [0x0c, 0xc1] (by decide)) ri_push  -- c73 PUSH2 0x0cc1
  xjmp 0xcc1  -- c76 JUMP
  xjd 0xcc2  -- cc1 JUMPDEST
  xjd 0xcc3  -- cc2 JUMPDEST
  xs 0xcc4 (.reg (.dup 1)) (ri_dup (by rfl))  -- cc3 DUP2
  xl 0xcc5 0x320  -- cc4 MLOAD
  xs 0xcc7 (.push [0x01] (by decide)) ri_push  -- cc5 PUSH1 0x01
  xs 0xcc8 (.reg .add) ri_add  -- cc7 ADD
  xs 0xcc9 (.reg (.dup 0)) (ri_dup (by rfl))  -- cc8 DUP1
  xs 0xcca (.reg (.dup 3)) (ri_dup (by rfl))  -- cc9 DUP4
  xsw 0xccb 0x320  -- cca MSTORE
  xs 0xccc (.reg (.dup 1)) (ri_dup (by rfl))  -- ccb DUP2
  xs 0xccd (.reg .eq) ri_eq  -- ccc EQ
  xs 0xcce (.reg .iszero) ri_iszero  -- ccd ISZERO
  xs 0xcd1 (.push [0x0c, 0x1f] (by decide)) ri_push  -- cce PUSH2 0x0c1f
  xji 0xcd2 0xc1f hw
  · exact absurd hw (by decide)
  exact ⟨_, _, _, .inl ⟨hd1, hadd, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩


/-- **Iteration 2** of the balance loop. -/
theorem xa_cta_it2 {M : Mem} {D0 amp B0 B1 B2 ck : B256}
    (hcode : sevm.code = code) (hck : ck = Bytes.toB256 [2])
    (hV : VW M [(0x320, ck), (0x200, D0), (0x140, B0), (0x160, B1), (0x180, B2), (0x1a0, amp)])
    (h : XAt sevm post 0xc1f (St b [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [3, 32]] M G) L) :
    ∃ v M' G', CtaUpd (ctaDep sevm) B2 (ctaAmt sevm 2) v ∧
      XAt sevm post 0xcd2 (St b [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [3, 32]] M' G') L ∧
      VW M' [(0x320, Bytes.toB256 [1] + Bytes.toB256 [2]), (0x200, D0), (0x140, B0), (0x160, B1), (0x180, v),
        (0x1a0, amp)] := by
  subst hck
  xjd 0xc20  -- c1f JUMPDEST
  xs 0xc22 (.push [0x64] (by decide)) ri_push  -- c20 PUSH1 0x64
  xs 0xc23 (.reg .calldataload) ri_calldataload  -- c22 CALLDATALOAD
  xs 0xc24 (.reg .iszero) ri_iszero  -- c23 ISZERO
  xs 0xc27 (.push [0x0c, 0x77] (by decide)) ri_push  -- c24 PUSH2 0x0c77
  xji 0xc28 0xc77 hw
  swap
  · have hd0 := eqCheck_ne_zero_eq hw
    clear hw
    xjd 0xc78  -- c77 JUMPDEST
    xs 0xc7b (.push [0x01, 0x40] (by decide)) ri_push  -- c78 PUSH2 0x0140
    xs 0xc7e (.push [0x03, 0x20] (by decide)) ri_push  -- c7b PUSH2 0x0320
    xl 0xc7f 0x320  -- c7e MLOAD
    xs 0xc81 (.push [0x03] (by decide)) ri_push  -- c7f PUSH1 0x03
    xs 0xc82 (.reg (.dup 1)) (ri_dup (by rfl))  -- c81 DUP2
    xs 0xc83 (.reg .lt) ri_lt  -- c82 LT
    xs 0xc86 (.push [0x0c, 0x8b] (by decide)) ri_push  -- c83 PUSH2 0x0c8b
    xji 0xc87 0xc8b hw
    · xdead
    clear hw
    xjd 0xc8c  -- c8b JUMPDEST
    xs 0xc8e (.push [0x20] (by decide)) ri_push  -- c8c PUSH1 0x20
    xs 0xc8f (.reg .mul) ri_mul  -- c8e MUL
    xs 0xc90 (.reg .add) ri_add  -- c8f ADD
    xs 0xc91 (.reg (.dup 0)) (ri_dup (by rfl))  -- c90 DUP1
    xl 0xc92 0x180  -- c91 MLOAD
    xs 0xc94 (.push [0x04] (by decide)) ri_push  -- c92 PUSH1 0x04
    xs 0xc97 (.push [0x03, 0x20] (by decide)) ri_push  -- c94 PUSH2 0x0320
    xl 0xc98 0x320  -- c97 MLOAD
    xs 0xc9a (.push [0x03] (by decide)) ri_push  -- c98 PUSH1 0x03
    xs 0xc9b (.reg (.dup 1)) (ri_dup (by rfl))  -- c9a DUP2
    xs 0xc9c (.reg .lt) ri_lt  -- c9b LT
    xs 0xc9f (.push [0x0c, 0xa4] (by decide)) ri_push  -- c9c PUSH2 0x0ca4
    xji 0xca0 0xca4 hw
    · xdead
    clear hw
    xjd 0xca5  -- ca4 JUMPDEST
    xs 0xca7 (.push [0x20] (by decide)) ri_push  -- ca5 PUSH1 0x20
    xs 0xca8 (.reg .mul) ri_mul  -- ca7 MUL
    xs 0xca9 (.reg .add) ri_add  -- ca8 ADD
    xs 0xcaa (.reg .calldataload) ri_calldataload  -- ca9 CALLDATALOAD
    xs 0xcab (.reg (.dup 0)) (ri_dup (by rfl))  -- caa DUP1
    xs 0xcac (.reg (.dup 2)) (ri_dup (by rfl))  -- cab DUP3
    xs 0xcad (.reg .lt) ri_lt  -- cac LT
    xs 0xcae (.reg .iszero) ri_iszero  -- cad ISZERO
    xs 0xcb1 (.push [0x0c, 0xb6] (by decide)) ri_push  -- cae PUSH2 0x0cb6
    xji 0xcb2 0xcb6 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xjd 0xcb7  -- cb6 JUMPDEST
    xs 0xcb8 (.reg (.dup 0)) (ri_dup (by rfl))  -- cb7 DUP1
    xs 0xcb9 (.reg (.dup 2)) (ri_dup (by rfl))  -- cb8 DUP3
    xs 0xcba (.reg .sub) ri_sub  -- cb9 SUB
    xs 0xcbb (.reg (.swap 0)) (ri_swap (by rfl))  -- cba SWAP1
    xs 0xcbc (.reg .pop) ri_pop  -- cbb POP
    xs 0xcbd (.reg (.swap 0)) (ri_swap (by rfl))  -- cbc SWAP1
    xs 0xcbe (.reg .pop) ri_pop  -- cbd POP
    xs 0xcbf (.reg (.dup 1)) (ri_dup (by rfl))  -- cbe DUP2
    xsw 0xcc0 0x180  -- cbf MSTORE
    xs 0xcc1 (.reg .pop) ri_pop  -- cc0 POP
    xjd 0xcc2  -- cc1 JUMPDEST
    xjd 0xcc3  -- cc2 JUMPDEST
    xs 0xcc4 (.reg (.dup 1)) (ri_dup (by rfl))  -- cc3 DUP2
    xl 0xcc5 0x320  -- cc4 MLOAD
    xs 0xcc7 (.push [0x01] (by decide)) ri_push  -- cc5 PUSH1 0x01
    xs 0xcc8 (.reg .add) ri_add  -- cc7 ADD
    xs 0xcc9 (.reg (.dup 0)) (ri_dup (by rfl))  -- cc8 DUP1
    xs 0xcca (.reg (.dup 3)) (ri_dup (by rfl))  -- cc9 DUP4
    xsw 0xccb 0x320  -- cca MSTORE
    xs 0xccc (.reg (.dup 1)) (ri_dup (by rfl))  -- ccb DUP2
    xs 0xccd (.reg .eq) ri_eq  -- ccc EQ
    xs 0xcce (.reg .iszero) ri_iszero  -- ccd ISZERO
    xs 0xcd1 (.push [0x0c, 0x1f] (by decide)) ri_push  -- cce PUSH2 0x0c1f
    xji 0xcd2 0xc1f hw
    swap
    · exact absurd hw (by decide)
    exact ⟨_, _, _, .inr ⟨hd0, hle, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have hd1 := eqCheck_eq_zero hw
  clear hw
  xs 0xc2b (.push [0x01, 0x40] (by decide)) ri_push  -- c28 PUSH2 0x0140
  xs 0xc2e (.push [0x03, 0x20] (by decide)) ri_push  -- c2b PUSH2 0x0320
  xl 0xc2f 0x320  -- c2e MLOAD
  xs 0xc31 (.push [0x03] (by decide)) ri_push  -- c2f PUSH1 0x03
  xs 0xc32 (.reg (.dup 1)) (ri_dup (by rfl))  -- c31 DUP2
  xs 0xc33 (.reg .lt) ri_lt  -- c32 LT
  xs 0xc36 (.push [0x0c, 0x3b] (by decide)) ri_push  -- c33 PUSH2 0x0c3b
  xji 0xc37 0xc3b hw
  · xdead
  clear hw
  xjd 0xc3c  -- c3b JUMPDEST
  xs 0xc3e (.push [0x20] (by decide)) ri_push  -- c3c PUSH1 0x20
  xs 0xc3f (.reg .mul) ri_mul  -- c3e MUL
  xs 0xc40 (.reg .add) ri_add  -- c3f ADD
  xs 0xc41 (.reg (.dup 0)) (ri_dup (by rfl))  -- c40 DUP1
  xl 0xc42 0x180  -- c41 MLOAD
  xs 0xc44 (.push [0x04] (by decide)) ri_push  -- c42 PUSH1 0x04
  xs 0xc47 (.push [0x03, 0x20] (by decide)) ri_push  -- c44 PUSH2 0x0320
  xl 0xc48 0x320  -- c47 MLOAD
  xs 0xc4a (.push [0x03] (by decide)) ri_push  -- c48 PUSH1 0x03
  xs 0xc4b (.reg (.dup 1)) (ri_dup (by rfl))  -- c4a DUP2
  xs 0xc4c (.reg .lt) ri_lt  -- c4b LT
  xs 0xc4f (.push [0x0c, 0x54] (by decide)) ri_push  -- c4c PUSH2 0x0c54
  xji 0xc50 0xc54 hw
  · xdead
  clear hw
  xjd 0xc55  -- c54 JUMPDEST
  xs 0xc57 (.push [0x20] (by decide)) ri_push  -- c55 PUSH1 0x20
  xs 0xc58 (.reg .mul) ri_mul  -- c57 MUL
  xs 0xc59 (.reg .add) ri_add  -- c58 ADD
  xs 0xc5a (.reg .calldataload) ri_calldataload  -- c59 CALLDATALOAD
  xs 0xc5b (.reg (.dup 1)) (ri_dup (by rfl))  -- c5a DUP2
  xs 0xc5c (.reg (.dup 1)) (ri_dup (by rfl))  -- c5b DUP2
  xs 0xc5d (.reg (.dup 3)) (ri_dup (by rfl))  -- c5c DUP4
  xs 0xc5e (.reg .add) ri_add  -- c5d ADD
  xs 0xc5f (.reg .lt) ri_lt  -- c5e LT
  xs 0xc60 (.reg .iszero) ri_iszero  -- c5f ISZERO
  xs 0xc63 (.push [0x0c, 0x68] (by decide)) ri_push  -- c60 PUSH2 0x0c68
  xji 0xc64 0xc68 hw
  · xdead
  have hadd := (B256.nof_iff_not_add_lt _ _).mpr
    (ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xjd 0xc69  -- c68 JUMPDEST
  xs 0xc6a (.reg (.dup 0)) (ri_dup (by rfl))  -- c69 DUP1
  xs 0xc6b (.reg (.dup 2)) (ri_dup (by rfl))  -- c6a DUP3
  xs 0xc6c (.reg .add) ri_add  -- c6b ADD
  xs 0xc6d (.reg (.swap 0)) (ri_swap (by rfl))  -- c6c SWAP1
  xs 0xc6e (.reg .pop) ri_pop  -- c6d POP
  xs 0xc6f (.reg (.swap 0)) (ri_swap (by rfl))  -- c6e SWAP1
  xs 0xc70 (.reg .pop) ri_pop  -- c6f POP
  xs 0xc71 (.reg (.dup 1)) (ri_dup (by rfl))  -- c70 DUP2
  xsw 0xc72 0x180  -- c71 MSTORE
  xs 0xc73 (.reg .pop) ri_pop  -- c72 POP
  xs 0xc76 (.push [0x0c, 0xc1] (by decide)) ri_push  -- c73 PUSH2 0x0cc1
  xjmp 0xcc1  -- c76 JUMP
  xjd 0xcc2  -- cc1 JUMPDEST
  xjd 0xcc3  -- cc2 JUMPDEST
  xs 0xcc4 (.reg (.dup 1)) (ri_dup (by rfl))  -- cc3 DUP2
  xl 0xcc5 0x320  -- cc4 MLOAD
  xs 0xcc7 (.push [0x01] (by decide)) ri_push  -- cc5 PUSH1 0x01
  xs 0xcc8 (.reg .add) ri_add  -- cc7 ADD
  xs 0xcc9 (.reg (.dup 0)) (ri_dup (by rfl))  -- cc8 DUP1
  xs 0xcca (.reg (.dup 3)) (ri_dup (by rfl))  -- cc9 DUP4
  xsw 0xccb 0x320  -- cca MSTORE
  xs 0xccc (.reg (.dup 1)) (ri_dup (by rfl))  -- ccb DUP2
  xs 0xccd (.reg .eq) ri_eq  -- ccc EQ
  xs 0xcce (.reg .iszero) ri_iszero  -- ccd ISZERO
  xs 0xcd1 (.push [0x0c, 0x1f] (by decide)) ri_push  -- cce PUSH2 0x0c1f
  xji 0xcd2 0xc1f hw
  swap
  · exact absurd hw (by decide)
  exact ⟨_, _, _, .inl ⟨hd1, hadd, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩



/-- **The balance loop** (`0xc14` to the frame save's head `0xcdc`): each balance updated by
its amount per the deposit flag; the save pointer at `0x360`. -/
theorem xa_cta_loop {M : Mem} {D0 amp B0 B1 B2 : B256}
    (hcode : sevm.code = code)
    (hV : VW M [(0x200, D0), (0x140, B0), (0x160, B1), (0x180, B2), (0x1a0, amp)])
    (h : XAt sevm post 0xc14 (St b [] M G) L) :
    ∃ v0 v1 v2 M' G', CtaUpd (ctaDep sevm) B0 (ctaAmt sevm 0) v0 ∧
      CtaUpd (ctaDep sevm) B1 (ctaAmt sevm 1) v1 ∧ CtaUpd (ctaDep sevm) B2 (ctaAmt sevm 2) v2 ∧
      XAt sevm post 0xcdc (St b [] M' G') L ∧
      VW M' [(0x360, Bytes.toB256 [1, 64]), (0x200, D0), (0x140, v0), (0x160, v1), (0x180, v2),
        (0x1a0, amp)] := by
  xs 0xc17 (.push [0x03, 0x20] (by decide)) ri_push  -- c14 PUSH2 0x0320
  xs 0xc19 (.push [0x00] (by decide)) ri_push  -- c17 PUSH1 0x00
  xs 0xc1b (.push [0x03] (by decide)) ri_push  -- c19 PUSH1 0x03
  xs 0xc1c (.reg (.dup 1)) (ri_dup (by rfl))  -- c1b DUP2
  xs 0xc1d (.reg (.dup 3)) (ri_dup (by rfl))  -- c1c DUP4
  xsw 0xc1e 0x320  -- c1d MSTORE
  xs 0xc1f (.reg .add) ri_add  -- c1e ADD
  obtain ⟨v0, M, _, hu0, h, hV1⟩ := xa_cta_it0 hcode rfl hV h
  clear hV
  obtain ⟨v1, M, _, hu1, h, hV⟩ := xa_cta_it1 hcode (by decide) hV1 h
  clear hV1
  obtain ⟨v2, M, _, hu2, h, hV1⟩ := xa_cta_it2 hcode (by decide) hV h
  clear hV
  have hV := hV1
  clear hV1
  xjd 0xcd3  -- cd2 JUMPDEST
  xs 0xcd4 (.reg .pop) ri_pop  -- cd3 POP
  xs 0xcd5 (.reg .pop) ri_pop  -- cd4 POP
  xs 0xcd8 (.push [0x01, 0x40] (by decide)) ri_push  -- cd5 PUSH2 0x0140
  xs 0xcdb (.push [0x03, 0x60] (by decide)) ri_push  -- cd8 PUSH2 0x0360
  xsw 0xcdc 0x360  -- cdb MSTORE
  refine ⟨v0, v1, v2, _, _, hu0, hu1, hu2, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
