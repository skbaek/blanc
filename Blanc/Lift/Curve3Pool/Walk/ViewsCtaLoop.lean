import Blanc.Lift.Curve3Pool.Walk.ViewsCta
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
  xa 5
  xji 0xc28 0xc77 hw
  swap
  · have hd0 := B256.eq_of_eqCheck_ne_zero hw
    clear hw
    xa 3
    xl 0xc7f 0x320  -- c7e MLOAD
    xa 4
    xji 0xc87 0xc8b hw
    · xdead
    clear hw
    xa 5
    xl 0xc92 0x140  -- c91 MLOAD
    xa 2
    xl 0xc98 0x320  -- c97 MLOAD
    xa 4
    xji 0xca0 0xca4 hw
    · xdead
    clear hw
    xa 10
    xji 0xcb2 0xcb6 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0xcc0 0x140  -- cbf MSTORE
    xa 4
    xl 0xcc5 0x320  -- cc4 MLOAD
    xa 4
    xsw 0xccb 0x320  -- cca MSTORE
    xa 4
    xji 0xcd2 0xc1f hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, .inr ⟨hd0, hle, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have hd1 := ne_of_eqCheck_eq_zero hw
  clear hw
  xa 2
  xl 0xc2f 0x320  -- c2e MLOAD
  xa 4
  xji 0xc37 0xc3b hw
  · xdead
  clear hw
  xa 5
  xl 0xc42 0x140  -- c41 MLOAD
  xa 2
  xl 0xc48 0x320  -- c47 MLOAD
  xa 4
  xji 0xc50 0xc54 hw
  · xdead
  clear hw
  xa 12
  xji 0xc64 0xc68 hw
  · xdead
  have hadd := (B256.nof_iff_not_add_lt _ _).mpr
    (B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xa 9
  xsw 0xc72 0x140  -- c71 MSTORE
  xa 2
  xjmp 0xcc1  -- c76 JUMP
  xa 3
  xl 0xcc5 0x320  -- cc4 MLOAD
  xa 4
  xsw 0xccb 0x320  -- cca MSTORE
  xa 4
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
  xa 5
  xji 0xc28 0xc77 hw
  swap
  · have hd0 := B256.eq_of_eqCheck_ne_zero hw
    clear hw
    xa 3
    xl 0xc7f 0x320  -- c7e MLOAD
    xa 4
    xji 0xc87 0xc8b hw
    · xdead
    clear hw
    xa 5
    xl 0xc92 0x160  -- c91 MLOAD
    xa 2
    xl 0xc98 0x320  -- c97 MLOAD
    xa 4
    xji 0xca0 0xca4 hw
    · xdead
    clear hw
    xa 10
    xji 0xcb2 0xcb6 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0xcc0 0x160  -- cbf MSTORE
    xa 4
    xl 0xcc5 0x320  -- cc4 MLOAD
    xa 4
    xsw 0xccb 0x320  -- cca MSTORE
    xa 4
    xji 0xcd2 0xc1f hw
    · exact absurd hw (by decide)
    exact ⟨_, _, _, .inr ⟨hd0, hle, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have hd1 := ne_of_eqCheck_eq_zero hw
  clear hw
  xa 2
  xl 0xc2f 0x320  -- c2e MLOAD
  xa 4
  xji 0xc37 0xc3b hw
  · xdead
  clear hw
  xa 5
  xl 0xc42 0x160  -- c41 MLOAD
  xa 2
  xl 0xc48 0x320  -- c47 MLOAD
  xa 4
  xji 0xc50 0xc54 hw
  · xdead
  clear hw
  xa 12
  xji 0xc64 0xc68 hw
  · xdead
  have hadd := (B256.nof_iff_not_add_lt _ _).mpr
    (B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xa 9
  xsw 0xc72 0x160  -- c71 MSTORE
  xa 2
  xjmp 0xcc1  -- c76 JUMP
  xa 3
  xl 0xcc5 0x320  -- cc4 MLOAD
  xa 4
  xsw 0xccb 0x320  -- cca MSTORE
  xa 4
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
  xa 5
  xji 0xc28 0xc77 hw
  swap
  · have hd0 := B256.eq_of_eqCheck_ne_zero hw
    clear hw
    xa 3
    xl 0xc7f 0x320  -- c7e MLOAD
    xa 4
    xji 0xc87 0xc8b hw
    · xdead
    clear hw
    xa 5
    xl 0xc92 0x180  -- c91 MLOAD
    xa 2
    xl 0xc98 0x320  -- c97 MLOAD
    xa 4
    xji 0xca0 0xca4 hw
    · xdead
    clear hw
    xa 10
    xji 0xcb2 0xcb6 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0xcc0 0x180  -- cbf MSTORE
    xa 4
    xl 0xcc5 0x320  -- cc4 MLOAD
    xa 4
    xsw 0xccb 0x320  -- cca MSTORE
    xa 4
    xji 0xcd2 0xc1f hw
    swap
    · exact absurd hw (by decide)
    exact ⟨_, _, _, .inr ⟨hd0, hle, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  have hd1 := ne_of_eqCheck_eq_zero hw
  clear hw
  xa 2
  xl 0xc2f 0x320  -- c2e MLOAD
  xa 4
  xji 0xc37 0xc3b hw
  · xdead
  clear hw
  xa 5
  xl 0xc42 0x180  -- c41 MLOAD
  xa 2
  xl 0xc48 0x320  -- c47 MLOAD
  xa 4
  xji 0xc50 0xc54 hw
  · xdead
  clear hw
  xa 12
  xji 0xc64 0xc68 hw
  · xdead
  have hadd := (B256.nof_iff_not_add_lt _ _).mpr
    (B256.not_lt_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xa 9
  xsw 0xc72 0x180  -- c71 MSTORE
  xa 2
  xjmp 0xcc1  -- c76 JUMP
  xa 3
  xl 0xcc5 0x320  -- cc4 MLOAD
  xa 4
  xsw 0xccb 0x320  -- cca MSTORE
  xa 4
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
  xa 5
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
  xa 5
  xsw 0xcdc 0x360  -- cdb MSTORE
  refine ⟨v0, v1, v2, _, _, hu0, hu1, hu2, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
