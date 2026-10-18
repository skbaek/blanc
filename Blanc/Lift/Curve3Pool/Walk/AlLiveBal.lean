import Blanc.Lift.Curve3Pool.Walk.AlLivePull

/-!
# `add_liquidity`, forward: the fee-index tests and the fee coin's two `balanceOf(self)` reads

`alFeeTest` (the test `i == FEE_INDEX` at `0x10c2`) and `alBal1` (the first `balanceOf(self)`,
`0x10ce` → the pull) are path skeletons with every context's tree an `rfl` instance.
`rx_al_feeTest` takes the pull arm (`i ≠ 2`) or the read arm (`i = 2`); `rx_al_bal1` reads
`in_amount = coin.balanceOf(self)` (`CoinBalOkAt`, window `0x53c`/`0x5a0`) into `0x4e0`.
`rx_al_joinPlain` and `rx_al_joinFee` run the test after the pull (`t_1271_c5`) to the credit
`t_12d6_c6`; for coin `2` the second read (`0x87c`/`0x8e0`) and `in_amount = B2 - B1` (checked).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alFeeTest (a1 : SFunc) : SFunc :=
  (.next (.push [0x02] (by decide)) (.next (.push [0x04, 0xc0] (by decide)) (.next (.reg .mload) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x11, 0x0d] (by decide)) a1))))))

theorem t_10c2_c4_eq : t_10c2_c4 = alFeeTest (.branch .undefined t_110d_c4) := rfl
theorem t_10c2_c40_eq : t_10c2_c40 = alFeeTest (.branch .undefined t_110d_c40) := rfl
theorem t_10c2_c41_eq : t_10c2_c41 = alFeeTest (.branch t_10ce_c41 t_110d_c41) := rfl
theorem t_10c2_c66_eq : t_10c2_c66 = alFeeTest (.branch t_10ce_c66 .undefined) := rfl

def alBal1 (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) : SFunc :=
  (.next (.push [0x20] (by decide)) (.next (.push [0x05, 0xa0] (by decide)) (.next (.push [0x24] (by decide)) (.next (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) (.next (.push [0x05, 0x20] (by decide)) (.next (.reg .mstore) (.next (.reg .address) (.next (.push [0x05, 0x40] (by decide)) (.next (.reg .mstore) (.next (.push [0x05, 0x3c] (by decide)) (.next (.push [0x05, 0x00] (by decide)) (.next (.reg .mload) (.next (.reg .gas) (.next (.exec .staticcall) (.next (.push [0x10, 0xf4] (by decide)) (.branch a1 (.dest (.next (.push [0x1f] (by decide)) (.next (.reg .returndatasize) (.next (.reg .gt) (.next (.push [0x11, 0x01] (by decide)) (.branch a2 (.dest (.next (.push [0x00] (by decide)) (.next (.reg .pop) (.next (.push [0x05, 0xa0] (by decide)) (.next (.reg .mload) (.next (.push [0x04, 0xe0] (by decide)) (.next (.reg .mstore) a3)))))))))))))))))))))))))))))
theorem t_10ce_c41_eq : t_10ce_c41 = alBal1 t_10f0_c41 t_10fd_c41 t_110d_c41 := rfl
theorem t_10ce_c66_eq : t_10ce_c66 = alBal1 t_10f0_c66 t_10fd_c66 t_110d_c66 := rfl

/-- `i == FEE_INDEX` for a counter `i < 3`. -/
theorem al_fee_ne {i : Nat} (hi : i < 3) (h2 : i ≠ 2) :
    B256.eqCheck (B256.eqCheck (Nat.toB256 i) (Bytes.toB256 [2])) 0 ≠ 0 := by
  rcases three_cases hi with rfl | rfl | rfl
  · decide
  · decide
  · exact absurd rfl h2

/-- **The fee-index test, forward.** -/
theorem rx_al_feeTest {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G i s : Nat} {Q : Outcome → Prop} {a c : SFunc}
    (hi : i < 3) (hR : Mem.Reads M img) (hsz : M.size = s) (hs : 0x520 ≤ s) (hs32 : s % 32 = 0)
    (hctr : WordAt img 0x4c0 (Nat.toB256 i)) (hroom : S.length + 12 < 1024)
    (ka : i = 2 → SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) a Q)
    (kc : i ≠ 2 → SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) c Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M (G + 28)) (alFeeTest (.branch a c)) Q := by
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ hctr (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  by_cases h2 : i = 2
  · subst h2
    xr (rx_branch_zero' (by decide) ·)
    exact ka rfl
  · xr (rx_branch_succ (al_fee_ne hi h2) ·)
    exact kc h2

/-- **The fee coin's first `balanceOf(self)`, forward** (`0x10ce` → the pull; memory `0x520` grows
to `0x5c0`, or stays at `0x840`). -/
theorem rx_al_bal1 {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256}
    {M : Mem} {img : Bytes} {G R U : Nat} {Q : Outcome → Prop} {C B1 : B256} {a1 a2 a3 : SFunc}
    {s c1 c2 s' : Nat}
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0x520 ∧ c1 = 6 ∧ c2 = 6 ∧ s' = 0x5c0) ∨ (s = 0x840 ∧ c1 = 3 ∧ c2 = 3 ∧ s' = 0x840))
    (hc : WordAt img 0x500 C) (hbal : CoinBalOkAt sevm W W C B1 U 0x53c 0x5a0)
    (hG : 300 + U + R ≤ G) (hGb : G < 2 ^ 256) (hroom : S.length + 12 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = s' →
      (∀ o w, WordAt img o w → o + 32 ≤ 0x4e0 ∨ 0x4e0 + 32 ≤ o ∧ o + 32 ≤ 0x520 →
        WordAt img' o w) →
      WordAt img' 0x4e0 B1 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) a3 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alBal1 a1 a2 a3) Q := by
  have hWc := hL.wc
  have hc12 : c1 + c2 ≤ 12 := by omega
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 2 + 3 + 3 + 3 + c2 + 3 + 2 + c1 + 15 := ⟨G - 31 - c1 - c2, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x520) (c := c1) hR hW hsz rfl
    (by rcases hs with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> decide) ?_
  clear hR hW hsz M; intro M hR hW hsz
  xr (rx_address (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x540) (c := c2) hR hW hsz rfl
    (by rcases hs with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩ <;> decide) ?_
  clear hR hW hsz M; intro M hR hW hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x500) (v := C) hR hsz rfl
    ⟨by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide,
      by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide⟩ (by wautoH hc) (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [5, 60] = (0x53c : B256) by decide, show Bytes.toB256 [0x24] = (0x24 : B256) by decide,
    show Bytes.toB256 [5, 160] = (0x5a0 : B256) by decide, show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read (0x53c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget := by
    rw [hR.read, show (0x53c : B256).toNat = 0x53c by decide, show (0x24 : B256).toNat = 0x24 by decide]
    exact al_balanceOf_input _ _
  refine rxe_staticWord (o := 0x5a0) (s := s') hL hWc hbal (by omega) (by omega) (by hrs) hin hR hW rfl
    (by show memExtsSize M.size _ = _; rw [hsz]; rcases hs with ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ <;> decide)
    (by rcases hs with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA' hrd hgd1 hgd2
  clear hR hW hsz hin hL
  have hR := hR'; have hW := hW'; have hsz := hsz'; have hL := hLd; clear hR' hW' hsz' hLd
  obtain ⟨g2, hg2⟩ : ∃ g, d.gasLeft = g + 53 := ⟨d.gasLeft - 53, by omega⟩
  rw [hg2]
  have hs'' : 0x5c0 ≤ s' ∧ s' % 32 = 0 := by rcases hs with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> decide
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_returndatasize (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hrd]; exact ex_rds_gt hlen hlt) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x5a0) hR hsz rfl ⟨by omega, hs''.2⟩ (by hrs) ·)
  rw [ex_ans_read _ _ _ hlen, hA']
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreK (o := 0x4e0) hR hW hsz rfl ⟨by omega, hs''.2⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
  exact k d M _ g2 hL hR hW hsz (fun o w hw ho => by
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      refine WordAt.write_other ?_ (by rw [List.length_take]; omega)
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      exact hw)
    (by wauto) (by omega) (by omega)

theorem al_prog_6 : cert.prog[6]? = some t_12d5_c6 := rfl

/-- **After a plain pull, forward** (`t_1271_c5` → the credit `t_12d6_c6`, `i ≠ 2`). -/
theorem rx_al_joinPlain {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G i s : Nat} {Q : Outcome → Prop}
    (hi : i < 3) (h2 : i ≠ 2) (hR : Mem.Reads M img) (hsz : M.size = s) (hs : 0x520 ≤ s)
    (hs32 : s % 32 = 0) (hctr : WordAt img 0x4c0 (Nat.toB256 i)) (hroom : S.length + 12 < 1024)
    (k : SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) t_12d6_c6 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M (G + 30)) t_1271_c5 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ hctr (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branchTo_succ (al_fee_ne hi h2) al_prog_6 ·)
  xr (rx_dest ·)
  exact k

/-- **After the fee coin's pull, forward** (`t_1271_c5` → the credit `t_12d6_c6`, `i = 2`):
the second `balanceOf(self)` (`CoinBalOkAt`, window `0x87c`/`0x8e0`; memory `0x840` grows to
`0x900`) and `in_amount = B2 - B1` (checked) at `0x4e0`. -/
theorem rx_al_joinFee {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256}
    {M : Mem} {img : Bytes} {G R U : Nat} {Q : Outcome → Prop} {C B1 B2 : B256}
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x840)
    (hctr : WordAt img 0x4c0 (Nat.toB256 2)) (hc : WordAt img 0x500 C) (hb1 : WordAt img 0x4e0 B1)
    (hbal : CoinBalOkAt sevm W W C B2 U 0x87c 0x8e0) (hsub : ¬ B2 < B1)
    (hG : 400 + U + R ≤ G) (hGb : G < 2 ^ 256) (hroom : S.length + 12 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x900 →
      (∀ o w, WordAt img o w → o + 32 ≤ 0x4e0 ∨ 0x4e0 + 32 ≤ o ∧ o + 32 ≤ 0x860 →
        WordAt img' o w) →
      WordAt img' 0x4e0 (B2 - B1) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_12d6_c6 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) t_1271_c5 Q := by
  have hWc := hL.wc
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 76 := ⟨G - 76, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 2) hR hsz rfl ⟨by decide, by decide⟩ hctr (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branchTo_zero' (by decide) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x860) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x840 0x860 32 = 0x880 by decide] at hsz
  xr (rx_address (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x880) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x880 0x880 32 = 0x8a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x500) (v := C) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [8, 124] = (0x87c : B256) by decide, show Bytes.toB256 [0x24] = (0x24 : B256) by decide,
    show Bytes.toB256 [8, 224] = (0x8e0 : B256) by decide, show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read (0x87c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget := by
    rw [hR.read, show (0x87c : B256).toNat = 0x87c by decide, show (0x24 : B256).toNat = 0x24 by decide]
    exact al_balanceOf_input2 _ _
  refine rxe_staticWord (o := 0x8e0) (s := 0x900) hL hWc hbal (by omega) (by omega) (by hrs) hin hR hW rfl
    (by show memExtsSize M.size _ = _; rw [hsz]; decide) (by decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA' hrd hgd1 hgd2
  clear hR hW hsz hin hL
  have hR := hR'; have hW := hW'; have hsz := hsz'; have hL := hLd; clear hR' hW' hsz' hLd
  obtain ⟨g2, hg2⟩ : ∃ g, d.gasLeft = g + 105 := ⟨d.gasLeft - 105, by omega⟩
  rw [hg2]
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_returndatasize (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hrd]; exact ex_rds_gt hlen hlt) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x8e0) hR hsz rfl (by decide) (by hrs) ·)
  rw [ex_ans_read _ _ _ hlen, hA']
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4e0) (v := B1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hb1) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [ltCheck_eq_zero_of_le (by rw [← B256.le_iff_toNat_le_toNat]; exact not_lt.mp hsub)]; decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x4e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x900 0x4e0 32 = 0x900 by decide] at hsz
  xr (rx_dest ·)
  exact k d M _ g2 hL hR hW hsz (fun o w hw ho => by
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      refine WordAt.write_other ?_ (by rw [List.length_take]; omega)
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
      exact hw)
    (by wauto) (by omega) (by omega)

end Blanc.Lift.Curve3Pool
