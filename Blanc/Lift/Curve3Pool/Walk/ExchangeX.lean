import Blanc.Lift.Curve3Pool.Walk.ExchangeMid

/-!
# `exchange`, part 4: the credited amount and `x`

* `xa_ex_bal2` (`0x2667` → `0x26c9`): for `i == FEE_INDEX` the second `balanceOf(self)` and
  `dx_w_fee = balanceOf(self) - dx_w_fee` (checked) at `0x380`; otherwise nothing;
* `xa_ex_x` (`0x26c9` → the frame save at `0x2754`): `x = xp[i] + dx_w_fee * rates[i] /
  PRECISION` (checked) at `0x7a0`, and the save counter `0x7e0` set to `0x140`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The second `balanceOf(self)`** for `i == 2` (`0x2667` → `0x26c9`). -/
theorem xa_ex_bal2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hF : ExFrame img B X D C)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (h : XAt sevm post 0x2667 (St b [] M G) L) :
    (exI sevm ≠ 2 ∧ ∃ G', XAt sevm post 0x26c9 (St b [] M G') L) ∨
    (exI sevm = 2 ∧ ∃ c L' d M' img' G', L = c :: L' ∧ ExBal sevm b d C c ∧
      ¬ Bytes.toB256 (c.post.output.take 32) < D ∧ Mem.Reads M' img' ∧ Mem.Wf M' ∧
      ExFrame img' B X (Bytes.toB256 (c.post.output.take 32) - D) C ∧
      XAt sevm post 0x26c9 (St d [] M' G') L') := by
  xs 0x2669 (.push [0x02] (by decide)) ri_push
  xs 0x266b (.push [0x04] (by decide)) ri_push
  xs 0x266c (.reg .calldataload) ri_calldataload
  xs 0x266d (.reg .eq) ri_eq
  xs 0x266e (.reg .iszero) ri_iszero
  xs 0x2671 (.push [0x26, 0xc9] (by decide)) ri_push
  xji 0x2672 0x26c9 hw
  swap
  · exact .inl ⟨fun e => isNe_jump hw (e.trans (by decide)), _, h⟩
  have hi2 : exI sevm = 2 := (isNe_fall hw).trans (by decide)
  clear hw
  refine .inr ⟨hi2, ?_⟩
  xs 0x2674 (.push [0x20] (by decide)) ri_push
  xs 0x2677 (.push [0x07, 0x80] (by decide)) ri_push
  xs 0x2679 (.push [0x24] (by decide)) ri_push
  xs 0x267e (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) ri_push
  xs 0x2681 (.push [0x07, 0x00] (by decide)) ri_push
  xmo 0x2682 (.reg .mstore) (ri_mstore_imgAt (o := 0x700) rfl)
  xs 0x2683 (.reg .address) ri_address
  xs 0x2686 (.push [0x07, 0x20] (by decide)) ri_push
  xmo 0x2687 (.reg .mstore) (ri_mstore_imgAt (o := 0x720) rfl)
  xs 0x268a (.push [0x07, 0x1c] (by decide)) ri_push
  xs 0x268d (.push [0x03, 0xa0] (by decide)) ri_push
  xmo 0x268e (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hF.coin.read] at h
  xs 0x268f (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x2690) (i := 0x71c) (n := 0x24) (o := 0x780) (z := 0x20)
    hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M1, L1, h, hR, hW, hrd, hob, hstor, hlogs, hk⟩ := h
  xs 0x2693 (.push [0x26, 0x98] (by decide)) ri_push
  xji 0x2694 0x2698 hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, -, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre hcoin
  clear hk
  xjd 0x2699
  xs 0x269b (.push [0x1f] (by decide)) ri_push
  xs 0x269c (.reg .returndatasize) ri_returndatasize
  xs 0x269d (.reg .gt) ri_gt
  xs 0x26a0 (.push [0x26, 0xa5] (by decide)) ri_push
  xji 0x26a1 0x26a5 hw2
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := gtCheck_ne_zero hw2
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw2
  xjd 0x26a6
  xs 0x26a8 (.push [0x00] (by decide)) ri_push
  xs 0x26a9 (.reg .pop) ri_pop
  xs 0x26ac (.push [0x07, 0x80] (by decide)) ri_push
  xmo 0x26ad (.reg .mload) (ri_mload_imgAt (o := 0x780) rfl)
  rw [ex_slice_take hlen] at h
  xs 0x26b0 (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x26b1 (.reg .mload) (ri_mload_imgAt (o := 0x380) rfl)
  have hD : WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x700
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x720 sevm.currentTarget.toB256.toBytes)
      0x780 (out.take 32)) 0x380 D := by
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hF.dx ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take] <;> omega
  rw [hD.read] at h
  xs 0x26b2 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x26b3 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x26b4 (.reg .lt) ri_lt
  xs 0x26b5 (.reg .iszero) ri_iszero
  xs 0x26b8 (.push [0x26, 0xbd] (by decide)) ri_push
  xji 0x26b9 0x26bd hw
  · xdead
  have hle := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x26be
  xs 0x26bf (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x26c0 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x26c1 (.reg .sub) ri_sub
  xs 0x26c2 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x26c3 (.reg .pop) ri_pop
  xs 0x26c4 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x26c5 (.reg .pop) ri_pop
  xs 0x26c8 (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x26c9 (.reg .mstore) (ri_mstore_imgAt (o := 0x380) rfl)
  refine ⟨c, L1, d1, _, _, _, hL, ⟨htgt, ?_, hstat, by rw [hcout]; exact hlen, hclogs,
    hcpre, hcpost, hstor, hlogs, hout, hacc, hcodeK⟩, by rw [hcout]; exact hle, hR, hW, ?_, h⟩
  · rw [hdata, show (0x71c : Nat) = 0x700 + 0x1c from rfl, show (0x720 : Nat) = 0x700 + 0x20 from rfl,
      bal_input]
    rfl
  · rw [hcout]
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, WordAt.write_self _ _ _, ?_⟩
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        (hF.rate k hk) ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        (hF.old k hk) ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        (hF.xp k hk) ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        hF.coin ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega

/-- **`x`** (`0x26c9` → `0x2754`). -/
theorem xa_ex_x {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C : B256}
    (hcode : sevm.code = code) (hi3 : (exI sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hF : ExFrame img B X D C)
    (h : XAt sevm post 0x26c9 (St b [] M G) L) :
    (D * exRate (exI sevm).toNat / D = exRate (exI sevm).toNat ∨ D = 0) ∧
    ¬ X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0 < X (exI sevm).toNat ∧
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ ExFrame img' B X D C ∧
      WordAt img' 0x7a0 (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0) ∧
      WordAt img' 0x7e0 (Nat.toB256 0x140) ∧ XAt sevm post 0x2754 (St b [] M' G') L := by
  have hr := hF.rate _ hi3
  have hx := hF.xp _ hi3
  xjd 0x26ca
  xs 0x26cd (.push [0x02, 0x00] (by decide)) ri_push
  xs 0x26cf (.push [0x04] (by decide)) ri_push
  xs 0x26d0 (.reg .calldataload) ri_calldataload
  xs 0x26d2 (.push [0x03] (by decide)) ri_push
  xs 0x26d3 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x26d4 (.reg .lt) ri_lt
  xs 0x26d7 (.push [0x26, 0xdc] (by decide)) ri_push
  xji 0x26d8 0x26dc hw
  · xdead
  clear hw
  xjd 0x26dd
  xs 0x26df (.push [0x20] (by decide)) ri_push
  xs 0x26e0 (.reg .mul) ri_mul
  xs 0x26e1 (.reg .add) ri_add
  xmo 0x26e2 (.reg .mload) (ri_mload_imgAt (o := 0x200 + 32 * (exI sevm).toNat)
    (ex_off hi3 (by decide) (by decide)))
  rw [hx.read] at h
  xs 0x26e5 (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x26e6 (.reg .mload) (ri_mload_imgAt (o := 0x380) rfl)
  rw [hF.dx.read] at h
  xs 0x26e9 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x26eb (.push [0x04] (by decide)) ri_push
  xs 0x26ec (.reg .calldataload) ri_calldataload
  xs 0x26ee (.push [0x03] (by decide)) ri_push
  xs 0x26ef (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x26f0 (.reg .lt) ri_lt
  xs 0x26f3 (.push [0x26, 0xf8] (by decide)) ri_push
  xji 0x26f4 0x26f8 hw
  · xdead
  clear hw
  xjd 0x26f9
  xs 0x26fb (.push [0x20] (by decide)) ri_push
  xs 0x26fc (.reg .mul) ri_mul
  xs 0x26fd (.reg .add) ri_add
  xmo 0x26fe (.reg .mload) (ri_mload_imgAt (o := 0x140 + 32 * (exI sevm).toNat)
    (ex_off hi3 (by decide) (by decide)))
  rw [hr.read] at h
  xs 0x26ff (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2700 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2701 (.reg .mul) ri_mul
  xs 0x2702 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2703 (.reg .iszero) ri_iszero
  xs 0x2704 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2705 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2706 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x2707 (.reg .div) ri_div
  xs 0x2708 (.reg .eq) ri_eq
  xs 0x2709 (.reg .or) ri_or
  xs 0x270c (.push [0x27, 0x11] (by decide)) ri_push
  xji 0x270d 0x2711 hmul
  · xdead
  xjd 0x2712
  xs 0x2713 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2714 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2715 (.reg .pop) ri_pop
  xs 0x2716 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2717 (.reg .pop) ri_pop
  xs 0x2718 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2719 (.reg .pop) ri_pop
  xs 0x2722 (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push
  xs 0x2723 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2724 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2727 (.push [0x27, 0x2c] (by decide)) ri_push
  xji 0x2728 0x272c hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x272d
  xs 0x272e (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x272f (.reg .div) ri_div
  xs 0x2730 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2731 (.reg .pop) ri_pop
  xs 0x2732 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2733 (.reg .pop) ri_pop
  xs 0x2734 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2735 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2736 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x2737 (.reg .add) ri_add
  xs 0x2738 (.reg .lt) ri_lt
  xs 0x2739 (.reg .iszero) ri_iszero
  xs 0x273c (.push [0x27, 0x41] (by decide)) ri_push
  xji 0x273d 0x2741 hadd
  · xdead
  xjd 0x2742
  xs 0x2743 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2744 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2745 (.reg .add) ri_add
  xs 0x2746 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2747 (.reg .pop) ri_pop
  xs 0x2748 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2749 (.reg .pop) ri_pop
  xs 0x274c (.push [0x07, 0xa0] (by decide)) ri_push
  xmo 0x274d (.reg .mstore) (ri_mstore_imgAt (o := 0x7a0) rfl)
  xs 0x2750 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x2753 (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x2754 (.reg .mstore) (ri_mstore_imgAt (o := 0x7e0) rfl)
  have hmul' := or_ne_zero hmul
  refine ⟨hmul'.imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq,
    ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hadd), _, _, _, hR, hW, hF.mono fun o v hv ho =>
      (hv.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega),
    (WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega),
    WordAt.write_self _ _ _, h⟩

end Blanc.Lift.Curve3Pool
