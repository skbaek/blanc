import Blanc.Lift.Curve3Pool.Walk.ExchangeMid

/-!
# `exchange`, part 6: `dy`, the fee and the slippage check

From the frame restore's exit (`0x27fd`) to the admin-fee arithmetic (`0x296f`): `y` copied to
`0x7c0`; `dy = xp[j] - y - 1` (checked twice) at `0x920`; `dy_fee = dy * fee / FEE_DENOMINATOR`
(checked) at `0x940`; `dy = (dy - dy_fee) * PRECISION / rates[j]` (checked) at `0x920`; the
error string staged; `assert dy >= min_dy`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- `FEE_DENOMINATOR` as the runtime pushes it. -/
abbrev exFeeDen : B256 := Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]


theorem exRate_ne {k : Nat} : exRate k ≠ 0 := by
  unfold exRate; split <;> decide

/-- `exchange`'s output words: `dy = xp[j] - y - 1`, `dy_fee`, and the amount out. -/
abbrev exDy0 (xj y : B256) : B256 := xj - y - Bytes.toB256 [1]
abbrev exDyFee (xj y fee : B256) : B256 := exDy0 xj y * fee / exFeeDen
abbrev exDyOut (xj y fee r : B256) : B256 :=
  (exDy0 xj y - exDyFee xj y fee) * exR0 / r

/-- **`dy`** (`0x27fd` → `0x296f`). -/
theorem xa_ex_dy {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C y : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hj3 : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hF : ExFrame img B X D C) (hy : WordAt img 0x900 y)
    (h : XAt sevm post 0x27fd (St b [] M G) L) :
    ¬ X (exJ sevm).toNat < y ∧ ¬ X (exJ sevm).toNat - y < Bytes.toB256 [1] ∧
    (exDy0 (X (exJ sevm).toNat) y * (b.getStor sevm.currentTarget).get feeSlot /
        exDy0 (X (exJ sevm).toNat) y = (b.getStor sevm.currentTarget).get feeSlot ∨
      exDy0 (X (exJ sevm).toNat) y = 0) ∧
    ¬ exDy0 (X (exJ sevm).toNat) y <
      exDyFee (X (exJ sevm).toNat) y ((b.getStor sevm.currentTarget).get feeSlot) ∧
    ((exDy0 (X (exJ sevm).toNat) y -
        exDyFee (X (exJ sevm).toNat) y ((b.getStor sevm.currentTarget).get feeSlot)) * exR0 /
        (exDy0 (X (exJ sevm).toNat) y -
          exDyFee (X (exJ sevm).toNat) y ((b.getStor sevm.currentTarget).get feeSlot)) = exR0 ∨
      exDy0 (X (exJ sevm).toNat) y -
        exDyFee (X (exJ sevm).toNat) y ((b.getStor sevm.currentTarget).get feeSlot) = 0) ∧
    ¬ exDyOut (X (exJ sevm).toNat) y ((b.getStor sevm.currentTarget).get feeSlot)
        (exRate (exJ sevm).toNat) < exMinDy sevm ∧
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ ExFrame img' B X D C ∧
      WordAt img' 0x920 (exDyOut (X (exJ sevm).toNat) y
        ((b.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)) ∧
      WordAt img' 0x940 (exDyFee (X (exJ sevm).toNat) y
        ((b.getStor sevm.currentTarget).get feeSlot)) ∧
      XAt sevm post 0x2970 (St (afterSload sevm b feeSlot) [] M' G') L := by
  have hr := hF.rate _ hj3
  have hx := hF.xp _ hj3
  xs 0x2800 (.push [0x09, 0x00] (by decide)) ri_push
  xmo 0x2801 (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [hy.read] at h
  xs 0x2804 (.push [0x07, 0xc0] (by decide)) ri_push
  xmo 0x2805 (.reg .mstore) (ri_mstore_imgAt (o := 0x7c0) rfl)
  xs 0x2808 (.push [0x02, 0x00] (by decide)) ri_push
  xs 0x280a (.push [0x24] (by decide)) ri_push
  xs 0x280b (.reg .calldataload) ri_calldataload
  xs 0x280d (.push [0x03] (by decide)) ri_push
  xs 0x280e (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x280f (.reg .lt) ri_lt
  xs 0x2812 (.push [0x28, 0x17] (by decide)) ri_push
  xji 0x2813 0x2817 hw
  · xdead
  clear hw
  xjd 0x2818
  xs 0x281a (.push [0x20] (by decide)) ri_push
  xs 0x281b (.reg .mul) ri_mul
  xs 0x281c (.reg .add) ri_add
  xmo 0x281d (.reg .mload) (ri_mload_imgAt (o := 0x200 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hx.read] at h
  xs 0x2820 (.push [0x07, 0xc0] (by decide)) ri_push
  xmo 0x2821 (.reg .mload) (ri_mload_imgAt (o := 0x7c0) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x2822 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2823 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2824 (.reg .lt) ri_lt
  xs 0x2825 (.reg .iszero) ri_iszero
  xs 0x2828 (.push [0x28, 0x2d] (by decide)) ri_push
  xji 0x2829 0x282d hy1
  · xdead
  xjd 0x282e
  xs 0x282f (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2830 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2831 (.reg .sub) ri_sub
  xs 0x2832 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2833 (.reg .pop) ri_pop
  xs 0x2834 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2835 (.reg .pop) ri_pop
  xs 0x2837 (.push [0x01] (by decide)) ri_push
  xs 0x2838 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2839 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x283a (.reg .lt) ri_lt
  xs 0x283b (.reg .iszero) ri_iszero
  xs 0x283e (.push [0x28, 0x43] (by decide)) ri_push
  xji 0x283f 0x2843 hy2
  · xdead
  xjd 0x2844
  xs 0x2845 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2846 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2847 (.reg .sub) ri_sub
  xs 0x2848 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2849 (.reg .pop) ri_pop
  xs 0x284a (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x284b (.reg .pop) ri_pop
  xs 0x284e (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x284f (.reg .mstore) (ri_mstore_imgAt (o := 0x920) rfl)
  -- `dy_fee`
  xs 0x2852 (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2853 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x2855 (.push [0x02] (by decide)) ri_push
  xw 0x2856 (.reg .sload) ri_sload
  rw [getStorVal_eq, feeSlot_lit] at h
  xs 0x2857 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2858 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2859 (.reg .mul) ri_mul
  xs 0x285a (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x285b (.reg .iszero) ri_iszero
  xs 0x285c (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x285d (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x285e (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x285f (.reg .div) ri_div
  xs 0x2860 (.reg .eq) ri_eq
  xs 0x2861 (.reg .or) ri_or
  xs 0x2864 (.push [0x28, 0x69] (by decide)) ri_push
  xji 0x2865 0x2869 hm1
  · xdead
  xjd 0x286a
  xs 0x286b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x286c (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x286d (.reg .pop) ri_pop
  xs 0x286e (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x286f (.reg .pop) ri_pop
  xs 0x2870 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2871 (.reg .pop) ri_pop
  xs 0x2877 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push
  xs 0x2878 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2879 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x287c (.push [0x28, 0x81] (by decide)) ri_push
  xji 0x287d 0x2881 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x2882
  xs 0x2883 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2884 (.reg .div) ri_div
  xs 0x2885 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2886 (.reg .pop) ri_pop
  xs 0x2887 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2888 (.reg .pop) ri_pop
  xs 0x288b (.push [0x09, 0x40] (by decide)) ri_push
  xmo 0x288c (.reg .mstore) (ri_mstore_imgAt (o := 0x940) rfl)
  -- `dy = (dy - dy_fee) * PRECISION / rates[j]`
  xs 0x288f (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2890 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), Bytes.readWord_writeAt_self] at h
  xs 0x2893 (.push [0x09, 0x40] (by decide)) ri_push
  xmo 0x2894 (.reg .mload) (ri_mload_imgAt (o := 0x940) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x2895 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2896 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2897 (.reg .lt) ri_lt
  xs 0x2898 (.reg .iszero) ri_iszero
  xs 0x289b (.push [0x28, 0xa0] (by decide)) ri_push
  xji 0x289c 0x28a0 hf1
  · xdead
  xjd 0x28a1
  xs 0x28a2 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x28a3 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x28a4 (.reg .sub) ri_sub
  xs 0x28a5 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x28a6 (.reg .pop) ri_pop
  xs 0x28a7 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x28a8 (.reg .pop) ri_pop
  xs 0x28b1 (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push
  xs 0x28b2 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x28b3 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x28b4 (.reg .mul) ri_mul
  xs 0x28b5 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x28b6 (.reg .iszero) ri_iszero
  xs 0x28b7 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x28b8 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x28b9 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x28ba (.reg .div) ri_div
  xs 0x28bb (.reg .eq) ri_eq
  xs 0x28bc (.reg .or) ri_or
  xs 0x28bf (.push [0x28, 0xc4] (by decide)) ri_push
  xji 0x28c0 0x28c4 hm2
  · xdead
  xjd 0x28c5
  xs 0x28c6 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x28c7 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x28c8 (.reg .pop) ri_pop
  xs 0x28c9 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x28ca (.reg .pop) ri_pop
  xs 0x28cb (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x28cc (.reg .pop) ri_pop
  xs 0x28cf (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x28d1 (.push [0x24] (by decide)) ri_push
  xs 0x28d2 (.reg .calldataload) ri_calldataload
  xs 0x28d4 (.push [0x03] (by decide)) ri_push
  xs 0x28d5 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x28d6 (.reg .lt) ri_lt
  xs 0x28d9 (.push [0x28, 0xde] (by decide)) ri_push
  xji 0x28da 0x28de hw
  · xdead
  clear hw
  xjd 0x28df
  xs 0x28e1 (.push [0x20] (by decide)) ri_push
  xs 0x28e2 (.reg .mul) ri_mul
  xs 0x28e3 (.reg .add) ri_add
  xmo 0x28e4 (.reg .mload) (ri_mload_imgAt (o := 0x140 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hr.read] at h
  xs 0x28e5 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x28e6 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x28e9 (.push [0x28, 0xee] (by decide)) ri_push
  xji 0x28ea 0x28ee hw
  · exact absurd hw exRate_ne
  clear hw
  xjd 0x28ef
  xs 0x28f0 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x28f1 (.reg .div) ri_div
  xs 0x28f2 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x28f3 (.reg .pop) ri_pop
  xs 0x28f4 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x28f5 (.reg .pop) ri_pop
  xs 0x28f8 (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x28f9 (.reg .mstore) (ri_mstore_imgAt (o := 0x920) rfl)
  -- the error string and `assert dy >= min_dy`
  xs 0x28fe (.push [0x08, 0xc3, 0x79, 0xa0] (by decide)) ri_push
  xs 0x2901 (.push [0x09, 0x60] (by decide)) ri_push
  xmo 0x2902 (.reg .mstore) (ri_mstore_imgAt (o := 0x960) rfl)
  xs 0x2904 (.push [0x20] (by decide)) ri_push
  xs 0x2907 (.push [0x09, 0x80] (by decide)) ri_push
  xmo 0x2908 (.reg .mstore) (ri_mstore_imgAt (o := 0x980) rfl)
  xs 0x290a (.push [0x2e] (by decide)) ri_push
  xs 0x290d (.push [0x09, 0xa0] (by decide)) ri_push
  xmo 0x290e (.reg .mstore) (ri_mstore_imgAt (o := 0x9a0) rfl)
  xs 0x292f (.push [0x45, 0x78, 0x63, 0x68, 0x61, 0x6e, 0x67, 0x65, 0x20, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x65, 0x64, 0x20, 0x69, 0x6e, 0x20, 0x66, 0x65, 0x77, 0x65, 0x72, 0x20, 0x63, 0x6f, 0x69, 0x6e, 0x73] (by decide)) ri_push
  xs 0x2932 (.push [0x09, 0xc0] (by decide)) ri_push
  xmo 0x2933 (.reg .mstore) (ri_mstore_imgAt (o := 0x9c0) rfl)
  xs 0x2954 (.push [0x20, 0x74, 0x68, 0x61, 0x6e, 0x20, 0x65, 0x78, 0x70, 0x65, 0x63, 0x74, 0x65, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x2957 (.push [0x09, 0xe0] (by decide)) ri_push
  xmo 0x2958 (.reg .mstore) (ri_mstore_imgAt (o := 0x9e0) rfl)
  xs 0x295b (.push [0x09, 0xa0] (by decide)) ri_push
  xs 0x295c (.reg .pop) ri_pop
  xs 0x295e (.push [0x64] (by decide)) ri_push
  xs 0x295f (.reg .calldataload) ri_calldataload
  xs 0x2962 (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2963 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
    at h
  xs 0x2964 (.reg .lt) ri_lt
  xs 0x2965 (.reg .iszero) ri_iszero
  xs 0x2968 (.push [0x29, 0x6f] (by decide)) ri_push
  xji 0x2969 0x296f hmin
  · xs 0x296b (.push [0x84] (by decide)) ri_push
    xs 0x296e (.push [0x09, 0x7c] (by decide)) ri_push
    xrevert
  xjd 0x2970
  obtain ⟨img1, hR1, hI⟩ := Mem.Reads.forget hR
  refine ⟨ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hy1),
    ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hy2),
    (or_ne_zero hm1).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq,
    ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hf1),
    (or_ne_zero hm2).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq,
    ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hmin), _, img1, _, hR1, hW,
    hF.mono fun o v hv ho => by rw [hI]; wchain; exact hv, by rw [hI]; wchain,
    by rw [hI]; wchain, h⟩

/-- `exchange`'s admin share: `dy_fee * admin_fee / FEE_DENOMINATOR * PRECISION / rates[j]`. -/
abbrev exAdm0 (fee af : B256) : B256 := fee * af / exFeeDen
abbrev exAdm (fee af r : B256) : B256 := exAdm0 fee af * exR0 / r

/-- **The admin share and the new balances** (`0x2970` → `0x2ab4`). -/
theorem xa_ex_store {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C dyOut dyFee : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hi3 : (exI sevm).toNat < 3) (hj3 : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hF : ExFrame img B X D C)
    (hout : WordAt img 0x920 dyOut) (hfee : WordAt img 0x940 dyFee)
    (h : XAt sevm post 0x2970 (St b [] M G) L) :
    (dyFee * (b.getStor sevm.currentTarget).get adminFeeSlot / dyFee =
        (b.getStor sevm.currentTarget).get adminFeeSlot ∨ dyFee = 0) ∧
    (exAdm0 dyFee ((b.getStor sevm.currentTarget).get adminFeeSlot) * exR0 /
        exAdm0 dyFee ((b.getStor sevm.currentTarget).get adminFeeSlot) = exR0 ∨
      exAdm0 dyFee ((b.getStor sevm.currentTarget).get adminFeeSlot) = 0) ∧
    ¬ B (exI sevm).toNat + D < B (exI sevm).toNat ∧ ¬ B (exJ sevm).toNat < dyOut ∧
    ¬ B (exJ sevm).toNat - dyOut <
      exAdm dyFee ((b.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat) ∧
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧
      (∀ o v, WordAt img o v → (o + 32 ≤ 0xc0 ∨ 0xe0 ≤ o) → (o + 32 ≤ 0xa20 ∨ 0xa40 ≤ o) →
        WordAt img' o v) ∧
      XAt sevm post 0x2ab4 (St (afterSstore sevm (afterSstore sevm (afterSload sevm b adminFeeSlot)
        (balancesBase + exI sevm) (B (exI sevm).toNat + D)) (balancesBase + exJ sevm)
        (B (exJ sevm).toNat - dyOut -
          exAdm dyFee ((b.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat)))
        [] M' G') L := by
  have hrj := hF.rate _ hj3
  have hoi := hF.old _ hi3
  have hoj := hF.old _ hj3
  xs 0x2973 (.push [0x09, 0x40] (by decide)) ri_push
  xmo 0x2974 (.reg .mload) (ri_mload_imgAt (o := 0x940) rfl)
  rw [hfee.read] at h
  xs 0x2976 (.push [0x03] (by decide)) ri_push
  xw 0x2977 (.reg .sload) ri_sload
  rw [getStorVal_eq, adminFeeSlot_lit] at h
  xs 0x2978 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2979 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x297a (.reg .mul) ri_mul
  xs 0x297b (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x297c (.reg .iszero) ri_iszero
  xs 0x297d (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x297e (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x297f (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x2980 (.reg .div) ri_div
  xs 0x2981 (.reg .eq) ri_eq
  xs 0x2982 (.reg .or) ri_or
  xs 0x2985 (.push [0x29, 0x8a] (by decide)) ri_push
  xji 0x2986 0x298a hm1
  · xdead
  xjd 0x298b
  xs 0x298c (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x298d (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x298e (.reg .pop) ri_pop
  xs 0x298f (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2990 (.reg .pop) ri_pop
  xs 0x2991 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2992 (.reg .pop) ri_pop
  xs 0x2998 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push
  xs 0x2999 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x299a (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x299d (.push [0x29, 0xa2] (by decide)) ri_push
  xji 0x299e 0x29a2 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x29a3
  xs 0x29a4 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x29a5 (.reg .div) ri_div
  xs 0x29a6 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x29a7 (.reg .pop) ri_pop
  xs 0x29a8 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x29a9 (.reg .pop) ri_pop
  xs 0x29ac (.push [0x0a, 0x20] (by decide)) ri_push
  xmo 0x29ad (.reg .mstore) (ri_mstore_imgAt (o := 0xa20) rfl)
  xs 0x29b0 (.push [0x0a, 0x20] (by decide)) ri_push
  xmo 0x29b1 (.reg .mload) (ri_mload_imgAt (o := 0xa20) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x29ba (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push
  xs 0x29bb (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x29bc (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x29bd (.reg .mul) ri_mul
  xs 0x29be (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x29bf (.reg .iszero) ri_iszero
  xs 0x29c0 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x29c1 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x29c2 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x29c3 (.reg .div) ri_div
  xs 0x29c4 (.reg .eq) ri_eq
  xs 0x29c5 (.reg .or) ri_or
  xs 0x29c8 (.push [0x29, 0xcd] (by decide)) ri_push
  xji 0x29c9 0x29cd hm2
  · xdead
  xjd 0x29ce
  xs 0x29cf (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x29d0 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x29d1 (.reg .pop) ri_pop
  xs 0x29d2 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x29d3 (.reg .pop) ri_pop
  xs 0x29d4 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x29d5 (.reg .pop) ri_pop
  xs 0x29d8 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x29da (.push [0x24] (by decide)) ri_push
  xs 0x29db (.reg .calldataload) ri_calldataload
  xs 0x29dd (.push [0x03] (by decide)) ri_push
  xs 0x29de (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x29df (.reg .lt) ri_lt
  xs 0x29e2 (.push [0x29, 0xe7] (by decide)) ri_push
  xji 0x29e3 0x29e7 hw
  · xdead
  clear hw
  xjd 0x29e8
  xs 0x29ea (.push [0x20] (by decide)) ri_push
  xs 0x29eb (.reg .mul) ri_mul
  xs 0x29ec (.reg .add) ri_add
  xmo 0x29ed (.reg .mload) (ri_mload_imgAt (o := 0x140 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hrj.read] at h
  xs 0x29ee (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x29ef (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x29f2 (.push [0x29, 0xf7] (by decide)) ri_push
  xji 0x29f3 0x29f7 hw
  · exact absurd hw exRate_ne
  clear hw
  xjd 0x29f8
  xs 0x29f9 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x29fa (.reg .div) ri_div
  xs 0x29fb (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x29fc (.reg .pop) ri_pop
  xs 0x29fd (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x29fe (.reg .pop) ri_pop
  xs 0x2a01 (.push [0x0a, 0x20] (by decide)) ri_push
  xmo 0x2a02 (.reg .mstore) (ri_mstore_imgAt (o := 0xa20) rfl)
  -- `self.balances[i] = old_balances[i] + dx_w_fee`
  xs 0x2a05 (.push [0x01, 0xa0] (by decide)) ri_push
  xs 0x2a07 (.push [0x04] (by decide)) ri_push
  xs 0x2a08 (.reg .calldataload) ri_calldataload
  xs 0x2a0a (.push [0x03] (by decide)) ri_push
  xs 0x2a0b (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2a0c (.reg .lt) ri_lt
  xs 0x2a0f (.push [0x2a, 0x14] (by decide)) ri_push
  xji 0x2a10 0x2a14 hw
  · xdead
  clear hw
  xjd 0x2a15
  xs 0x2a17 (.push [0x20] (by decide)) ri_push
  xs 0x2a18 (.reg .mul) ri_mul
  xs 0x2a19 (.reg .add) ri_add
  xmo 0x2a1a (.reg .mload) (ri_mload_imgAt (o := 0x1a0 + 32 * (exI sevm).toNat)
    (ex_off hi3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hoi.read] at h
  xs 0x2a1d (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x2a1e (.reg .mload) (ri_mload_imgAt (o := 0x380) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hF.dx.read] at h
  xs 0x2a1f (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2a20 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2a21 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x2a22 (.reg .add) ri_add
  xs 0x2a23 (.reg .lt) ri_lt
  xs 0x2a24 (.reg .iszero) ri_iszero
  xs 0x2a27 (.push [0x2a, 0x2c] (by decide)) ri_push
  xji 0x2a28 0x2a2c hadd
  · xdead
  xjd 0x2a2d
  xs 0x2a2e (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2a2f (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2a30 (.reg .add) ri_add
  xs 0x2a31 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2a32 (.reg .pop) ri_pop
  xs 0x2a33 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2a34 (.reg .pop) ri_pop
  xs 0x2a36 (.push [0x04] (by decide)) ri_push
  xs 0x2a37 (.reg .calldataload) ri_calldataload
  xs 0x2a39 (.push [0x03] (by decide)) ri_push
  xs 0x2a3a (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2a3b (.reg .lt) ri_lt
  xs 0x2a3e (.push [0x2a, 0x43] (by decide)) ri_push
  xji 0x2a3f 0x2a43 hw
  · xdead
  clear hw
  xjd 0x2a44
  xs 0x2a46 (.push [0x01] (by decide)) ri_push
  xs 0x2a48 (.push [0xc0] (by decide)) ri_push
  xmo 0x2a49 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x2a4b (.push [0x20] (by decide)) ri_push
  xs 0x2a4d (.push [0xc0] (by decide)) ri_push
  xmo 0x2a4e (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x2a4f (.reg .add) ri_add
  xw 0x2a50 (.reg .sstore) ri_sstore
  -- `self.balances[j] = old_balances[j] - dy - dy_admin_fee`
  xs 0x2a53 (.push [0x01, 0xa0] (by decide)) ri_push
  xs 0x2a55 (.push [0x24] (by decide)) ri_push
  xs 0x2a56 (.reg .calldataload) ri_calldataload
  xs 0x2a58 (.push [0x03] (by decide)) ri_push
  xs 0x2a59 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2a5a (.reg .lt) ri_lt
  xs 0x2a5d (.push [0x2a, 0x62] (by decide)) ri_push
  xji 0x2a5e 0x2a62 hw
  · xdead
  clear hw
  xjd 0x2a63
  xs 0x2a65 (.push [0x20] (by decide)) ri_push
  xs 0x2a66 (.reg .mul) ri_mul
  xs 0x2a67 (.reg .add) ri_add
  xmo 0x2a68 (.reg .mload) (ri_mload_imgAt (o := 0x1a0 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hoj.read] at h
  xs 0x2a6b (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2a6c (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hout.read] at h
  xs 0x2a6d (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2a6e (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2a6f (.reg .lt) ri_lt
  xs 0x2a70 (.reg .iszero) ri_iszero
  xs 0x2a73 (.push [0x2a, 0x78] (by decide)) ri_push
  xji 0x2a74 0x2a78 hs1
  · xdead
  xjd 0x2a79
  xs 0x2a7a (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2a7b (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2a7c (.reg .sub) ri_sub
  xs 0x2a7d (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2a7e (.reg .pop) ri_pop
  xs 0x2a7f (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2a80 (.reg .pop) ri_pop
  xs 0x2a83 (.push [0x0a, 0x20] (by decide)) ri_push
  xmo 0x2a84 (.reg .mload) (ri_mload_imgAt (o := 0xa20) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
    at h
  xs 0x2a85 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2a86 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2a87 (.reg .lt) ri_lt
  xs 0x2a88 (.reg .iszero) ri_iszero
  xs 0x2a8b (.push [0x2a, 0x90] (by decide)) ri_push
  xji 0x2a8c 0x2a90 hs2
  · xdead
  xjd 0x2a91
  xs 0x2a92 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2a93 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2a94 (.reg .sub) ri_sub
  xs 0x2a95 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2a96 (.reg .pop) ri_pop
  xs 0x2a97 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2a98 (.reg .pop) ri_pop
  xs 0x2a9a (.push [0x24] (by decide)) ri_push
  xs 0x2a9b (.reg .calldataload) ri_calldataload
  xs 0x2a9d (.push [0x03] (by decide)) ri_push
  xs 0x2a9e (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2a9f (.reg .lt) ri_lt
  xs 0x2aa2 (.push [0x2a, 0xa7] (by decide)) ri_push
  xji 0x2aa3 0x2aa7 hw
  · xdead
  clear hw
  xjd 0x2aa8
  xs 0x2aaa (.push [0x01] (by decide)) ri_push
  xs 0x2aac (.push [0xc0] (by decide)) ri_push
  xmo 0x2aad (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x2aaf (.push [0x20] (by decide)) ri_push
  xs 0x2ab1 (.push [0xc0] (by decide)) ri_push
  xmo 0x2ab2 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x2ab3 (.reg .add) ri_add
  xw 0x2ab4 (.reg .sstore) ri_sstore
  refine ⟨(or_ne_zero hm1).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq,
    (or_ne_zero hm2).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq,
    ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hadd),
    ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hs1),
    ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hs2), _, _, _, hR, hW, fun o v hv h1 h2 => ?_, h⟩
  refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other hv ?_) ?_)
    ?_) ?_ <;> simp only [B256.length_toBytes] <;> omega

end Blanc.Lift.Curve3Pool
