import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.ExchangeMid
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
      XAt sevm post 0x2970 (St (afterSloadH sevm b feeSlot) [] M' G') L := by
  have hr := hF.rate _ hj3
  have hx := hF.xp _ hj3
  xs 0x2800 (.push [0x09, 0x00] (by decide)) ri_push
  xmo 0x2801 (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [hy.read] at h
  xs 0x2804 (.push [0x07, 0xc0] (by decide)) ri_push
  xmo 0x2805 (.reg .mstore) (ri_mstore_imgAt (o := 0x7c0) rfl)
  xa 7
  xji 0x2813 0x2817 hw
  · xdead
  clear hw
  xa 4
  xmo 0x281d (.reg .mload) (ri_mload_imgAt (o := 0x200 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hx.read] at h
  xs 0x2820 (.push [0x07, 0xc0] (by decide)) ri_push
  xmo 0x2821 (.reg .mload) (ri_mload_imgAt (o := 0x7c0) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xa 5
  xji 0x2829 0x282d hy1
  · xdead
  xa 14
  xji 0x283f 0x2843 hy2
  · xdead
  xa 9
  xmo 0x284f (.reg .mstore) (ri_mstore_imgAt (o := 0x920) rfl)
  -- `dy_fee`
  xs 0x2852 (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2853 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x2855 (.push [0x02] (by decide)) ri_push
  xw 0x2856 (.reg .sload) ri_sloadF
  rw [getStorVal_eq, feeSlot_lit] at h
  xa 12
  xji 0x2865 0x2869 hm1
  · xdead
  xa 12
  xji 0x287d 0x2881 hw
  · exact absurd hw (by decide)
  clear hw
  xa 8
  xmo 0x288c (.reg .mstore) (ri_mstore_imgAt (o := 0x940) rfl)
  -- `dy = (dy - dy_fee) * PRECISION / rates[j]`
  xs 0x288f (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2890 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), Bytes.readWord_writeAt_self] at h
  xs 0x2893 (.push [0x09, 0x40] (by decide)) ri_push
  xmo 0x2894 (.reg .mload) (ri_mload_imgAt (o := 0x940) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xa 5
  xji 0x289c 0x28a0 hf1
  · xdead
  xa 21
  xji 0x28c0 0x28c4 hm2
  · xdead
  xa 15
  xji 0x28da 0x28de hw
  · xdead
  clear hw
  xa 4
  xmo 0x28e4 (.reg .mload) (ri_mload_imgAt (o := 0x140 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hr.read] at h
  xa 3
  xji 0x28ea 0x28ee hw
  · exact absurd hw exRate_ne
  clear hw
  xa 8
  xmo 0x28f9 (.reg .mstore) (ri_mstore_imgAt (o := 0x920) rfl)
  -- the error string and `assert dy >= min_dy`
  xa 2
  xmo 0x2902 (.reg .mstore) (ri_mstore_imgAt (o := 0x960) rfl)
  xa 2
  xmo 0x2908 (.reg .mstore) (ri_mstore_imgAt (o := 0x980) rfl)
  xa 2
  xmo 0x290e (.reg .mstore) (ri_mstore_imgAt (o := 0x9a0) rfl)
  xa 2
  xmo 0x2933 (.reg .mstore) (ri_mstore_imgAt (o := 0x9c0) rfl)
  xa 2
  xmo 0x2958 (.reg .mstore) (ri_mstore_imgAt (o := 0x9e0) rfl)
  xa 5
  xmo 0x2963 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
    at h
  xa 3
  xji 0x2969 0x296f hmin
  · xs 0x296b (.push [0x84] (by decide)) ri_push
    xs 0x296e (.push [0x09, 0x7c] (by decide)) ri_push
    xrevert
  xjd 0x2970
  obtain ⟨img1, hR1, hI⟩ := Mem.Reads.forget hR
  refine ⟨B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hy1),
    B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hy2),
    (or_ne_zero hm1).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero,
    B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hf1),
    (or_ne_zero hm2).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero,
    B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hmin), _, img1, _, hR1, hW,
    hF.mono fun o v hv ho => by rw [hI]; wchain; exact hv, by rw [hI]; wchain,
    by rw [hI]; wchain, h⟩

/-- `exchange`'s admin share: `dy_fee * admin_fee / FEE_DENOMINATOR * PRECISION / rates[j]`. -/
abbrev exAdm0 (fee af : B256) : B256 := fee * af / exFeeDen
abbrev exAdm (fee af r : B256) : B256 := exAdm0 fee af * exR0 / r

/-- **The admin share and the new balances** (`0x2970` → `0x2ab4`). -/
theorem xa_ex_store {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C dyOut dyFee : B256}
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
      XAt sevm post 0x2ab4 (St (afterSstoreH sevm (afterSstoreH sevm (afterSloadH sevm b adminFeeSlot)
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
  xw 0x2977 (.reg .sload) ri_sloadF
  rw [getStorVal_eq, adminFeeSlot_lit] at h
  xa 12
  xji 0x2986 0x298a hm1
  · xdead
  xa 12
  xji 0x299e 0x29a2 hw
  · exact absurd hw (by decide)
  clear hw
  xa 8
  xmo 0x29ad (.reg .mstore) (ri_mstore_imgAt (o := 0xa20) rfl)
  xs 0x29b0 (.push [0x0a, 0x20] (by decide)) ri_push
  xmo 0x29b1 (.reg .mload) (ri_mload_imgAt (o := 0xa20) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xa 13
  xji 0x29c9 0x29cd hm2
  · xdead
  xa 15
  xji 0x29e3 0x29e7 hw
  · xdead
  clear hw
  xa 4
  xmo 0x29ed (.reg .mload) (ri_mload_imgAt (o := 0x140 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hrj.read] at h
  xa 3
  xji 0x29f3 0x29f7 hw
  · exact absurd hw exRate_ne
  clear hw
  xa 8
  xmo 0x2a02 (.reg .mstore) (ri_mstore_imgAt (o := 0xa20) rfl)
  -- `self.balances[i] = old_balances[i] + dx_w_fee`
  xa 7
  xji 0x2a10 0x2a14 hw
  · xdead
  clear hw
  xa 4
  xmo 0x2a1a (.reg .mload) (ri_mload_imgAt (o := 0x1a0 + 32 * (exI sevm).toNat)
    (ex_off hi3 (by decide) (by decide)))
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hoi.read] at h
  xs 0x2a1d (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x2a1e (.reg .mload) (ri_mload_imgAt (o := 0x380) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hF.dx.read] at h
  xa 7
  xji 0x2a28 0x2a2c hadd
  · xdead
  xa 14
  xji 0x2a3f 0x2a43 hw
  · xdead
  clear hw
  xa 3
  xmo 0x2a49 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xa 2
  xmo 0x2a4e (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x2a4f (.reg .add) ri_add
  xw 0x2a50 (.reg .sstore) ri_sstoreF
  -- `self.balances[j] = old_balances[j] - dy - dy_admin_fee`
  xa 7
  xji 0x2a5e 0x2a62 hw
  · xdead
  clear hw
  xa 4
  xmo 0x2a68 (.reg .mload) (ri_mload_imgAt (o := 0x1a0 + 32 * (exJ sevm).toNat)
    (ex_off hj3 (by decide) (by decide)))
  simp (disch := omega) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hoj.read] at h
  xs 0x2a6b (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2a6c (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hout.read] at h
  xa 5
  xji 0x2a74 0x2a78 hs1
  · xdead
  xa 9
  xmo 0x2a84 (.reg .mload) (ri_mload_imgAt (o := 0xa20) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
    at h
  xa 5
  xji 0x2a8c 0x2a90 hs2
  · xdead
  xa 14
  xji 0x2aa3 0x2aa7 hw
  · xdead
  clear hw
  xa 3
  xmo 0x2aad (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xa 2
  xmo 0x2ab2 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x2ab3 (.reg .add) ri_add
  xw 0x2ab4 (.reg .sstore) ri_sstoreF
  refine ⟨(or_ne_zero hm1).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero,
    (or_ne_zero hm2).imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero,
    B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hadd),
    B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hs1),
    B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hs2), _, _, _, hR, hW, fun o v hv h1 h2 => ?_, h⟩
  refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other hv ?_) ?_)
    ?_) ?_ <;> simp only [B256.length_toBytes] <;> omega

end Blanc.Lift.Curve3Pool
