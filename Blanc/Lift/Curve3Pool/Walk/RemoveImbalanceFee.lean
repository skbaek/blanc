import Blanc.Lift.Curve3Pool.Walk.Kit

/-!
# `remove_liquidity_imbalance`, part 2: the fee numerator and the `_A` call setup

From the supply check's landing (`0x30c5`) to the internal `_A` call's jump (`0x312a`):
`fee * 3` with its checked-mul guard (reverting on overflow), the discarded `/ 8`
quotient, the numerator stored at `0x1e0`, `admin_fee` stored at `0x200`, and the
eight words `0x140 … 0x220` pushed for the `_A` call.

`xa_rli_feeA` (`0x30c5` → `0x3104`): the fee and admin-fee words read from storage,
`A3 = F * 3` with `(A3 / F = 3 ∨ F = 0)`, and the memory image with `A3` at `0x1e0`
and `AF` at `0x200`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`remove_liquidity_imbalance` fee numerator** (see the module note). -/
theorem xa_rli_feeA {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x30c5 (St b [] M G) L) :
    ∃ (F A3 Q AF : B256) (M1 : Mem) (G1 : Nat) (img1 : Bytes),
      F = b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]) ∧
      A3 = F * Bytes.toB256 [0x03] ∧
      (A3 / F = Bytes.toB256 [0x03] ∨ F = 0) ∧
      Q = A3 / Bytes.toB256 [0x08] ∧
      AF = (afterSload sevm b (Bytes.toB256 [0x02])).getStorVal sevm.currentTarget
        (Bytes.toB256 [0x03]) ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      WordAt img1 0x1e0 Q ∧ WordAt img1 0x200 AF ∧
      XAt sevm post 0x3104
        (St (afterSload sevm (afterSload sevm b (Bytes.toB256 [0x02])) (Bytes.toB256 [0x03]))
          [] M1 G1) L := by
  xjd 0x30c6
  xs 0x30c8 (.push [0x02] (by decide)) ri_push
  xw 0x30c9 (.reg .sload) ri_sload
  xs 0x30cb (.push [0x03] (by decide)) ri_push
  xs 0x30cc (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30cd (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30ce (.reg .mul) ri_mul
  xs 0x30cf (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30d0 (.reg .iszero) ri_iszero
  xs 0x30d1 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30d2 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x30d3 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x30d4 (.reg .div) ri_div
  xs 0x30d5 (.reg .eq) ri_eq
  xs 0x30d6 (.reg .or) ri_or
  xs 0x30d9 (.push [0x30, 0xde] (by decide)) ri_push
  xji 0x30da 0x30de hchk
  · xdead
  xjd 0x30df
  xs 0x30e0 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30e1 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30e2 (.reg .pop) ri_pop
  xs 0x30e3 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30e4 (.reg .pop) ri_pop
  xs 0x30e5 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30e6 (.reg .pop) ri_pop
  xs 0x30e8 (.push [0x08] (by decide)) ri_push
  xs 0x30e9 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30ea (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30ed (.push [0x30, 0xf2] (by decide)) ri_push
  xji 0x30ee 0x30f2 hw8
  · exact absurd hw8 (by decide)
  xjd 0x30f3
  xs 0x30f4 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30f5 (.reg .div) ri_div
  xs 0x30f6 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30f7 (.reg .pop) ri_pop
  xs 0x30f8 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30f9 (.reg .pop) ri_pop
  xs 0x30fc (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x30fd (.reg .mstore) (ri_mstore_imgAt (o := 0x1e0) rfl)
  xs 0x30ff (.push [0x03] (by decide)) ri_push
  xw 0x3100 (.reg .sload) ri_sload
  xs 0x3103 (.push [0x02, 0x00] (by decide)) ri_push
  xmo 0x3104 (.reg .mstore) (ri_mstore_imgAt (o := 0x200) rfl)
  refine ⟨b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]),
    b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]) * Bytes.toB256 [0x03],
    b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]) * Bytes.toB256 [0x03] /
      Bytes.toB256 [0x08],
    (afterSload sevm b (Bytes.toB256 [0x02])).getStorVal sevm.currentTarget (Bytes.toB256 [0x03]),
    M, _, _,
    rfl, rfl, (or_ne_zero hchk).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq, rfl, rfl,
    hR, hW, ?_, ?_, h⟩
  · exact WordAt.write_other (WordAt.write_self _ _ _) (Or.inl (by decide))
  · exact WordAt.write_self _ _ _

end Blanc.Lift.Curve3Pool
