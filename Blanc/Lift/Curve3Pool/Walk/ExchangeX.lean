import Blanc.Lift.Curve3Pool.Walk.ExchangeMid
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
  xa 6
  xji 0x2672 0x26c9 hw
  swap
  · exact .inl ⟨fun e => isNe_jump hw (e.trans (by decide)), _, h⟩
  have hi2 : exI sevm = 2 := (isNe_fall hw).trans (by decide)
  clear hw
  refine .inr ⟨hi2, ?_⟩
  xa 5
  xmo 0x2682 (.reg .mstore) (ri_mstore_imgAt (o := 0x700) rfl)
  xa 2
  xmo 0x2687 (.reg .mstore) (ri_mstore_imgAt (o := 0x720) rfl)
  xa 2
  xmo 0x268e (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hF.coin.read] at h
  xs 0x268f (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x2690) (i := 0x71c) (n := 0x24) (o := 0x780) (z := 0x20)
    hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M1, L1, h, _, hR, hW, hrd, hob, hstor, hlogs, hk⟩ := h
  xs 0x2693 (.push [0x26, 0x98] (by decide)) ri_push
  xji 0x2694 0x2698 hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, -, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre hcoin
  clear hk
  xa 5
  xji 0x26a1 0x26a5 hw2
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := B256.lt_of_gtCheck_ne_zero hw2
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw2
  xa 4
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
  xa 5
  xji 0x26b9 0x26bd hw
  · xdead
  have hle := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
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
  xa 8
  xji 0x26d8 0x26dc hw
  · xdead
  clear hw
  xa 4
  xmo 0x26e2 (.reg .mload) (ri_mload_imgAt (o := 0x200 + 32 * (exI sevm).toNat)
    (ex_off hi3 (by decide) (by decide)))
  rw [hx.read] at h
  xs 0x26e5 (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x26e6 (.reg .mload) (ri_mload_imgAt (o := 0x380) rfl)
  rw [hF.dx.read] at h
  xa 7
  xji 0x26f4 0x26f8 hw
  · xdead
  clear hw
  xa 4
  xmo 0x26fe (.reg .mload) (ri_mload_imgAt (o := 0x140 + 32 * (exI sevm).toNat)
    (ex_off hi3 (by decide) (by decide)))
  rw [hr.read] at h
  xa 12
  xji 0x270d 0x2711 hmul
  · xdead
  xa 12
  xji 0x2728 0x272c hw
  · exact absurd hw (by decide)
  clear hw
  xa 14
  xji 0x273d 0x2741 hadd
  · xdead
  xa 9
  xmo 0x274d (.reg .mstore) (ri_mstore_imgAt (o := 0x7a0) rfl)
  xa 2
  xmo 0x2754 (.reg .mstore) (ri_mstore_imgAt (o := 0x7e0) rfl)
  have hmul' := or_ne_zero hmul
  refine ⟨hmul'.imp B256.eq_of_eqCheck_ne_zero B256.eq_of_eqCheck_ne_zero,
    B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hadd), _, _, _, hR, hW, hF.mono fun o v hv ho =>
      (hv.write_other (by simp only [B256.length_toBytes]; omega)).write_other
        (by simp only [B256.length_toBytes]; omega),
    (WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega),
    WordAt.write_self _ _ _, h⟩

end Blanc.Lift.Curve3Pool
