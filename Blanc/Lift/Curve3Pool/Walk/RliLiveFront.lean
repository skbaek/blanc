import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveFrame

/-!
# `remove_liquidity_imbalance`, forward: the dispatcher, the guards, `_A` and the balances

`rx_dispatch_rli`: with the `remove_liquidity_imbalance` selector the frame's entry tree runs to
the arm's body `t_304f_c0`. `rx_rli_pre` (`t_304f_c0` → the first frame save `t_31b7_c0`): the
lock, no value, the pool alive, 3Crv's `totalSupply()` (`SupplyOkAt`, window `0x17c`/`0x1c0`)
at `0x140` and nonzero, the adjusted fee `fee · 3 / 8` (checked) at `0x1e0`, `admin_fee` at
`0x200`, `_A` (`a_exact`) at `0x220`, the balances at `0x280 … 0x2c0` and their copy at
`0x2e0 … 0x320`, and the save counter set.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The dispatcher, forward** (`remove_liquidity_imbalance`). -/
theorem rx_dispatch_rli {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_304f_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + 480)) t_0000_c0 Q := by
  have hR0 := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hsz0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hX : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD 0 32 0) = 0x9fdaea0c := by
    rw [vyImg_selector]; exact hsel
  have hlen4 : B256.eqCheck (B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [0x04]))
      0 ≠ 0 := by
    rw [ltCheck_eq_zero_of_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldatasize (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlen4 ·)
  xr (rx_dest ·)
  xr (rx_vyPrologue (by simp only [List.length_nil]; omega) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_zero' (by rw [hX]; decide) ·)

  exact k

theorem rli_prog_27 : cert.prog[27]? = some t_00a9_c27 := prog_27

/-- **The guards, the supply, `_A` and the balances, forward** (`t_304f_c0` → the first frame
save `t_31b7_c0`). -/
theorem rx_rli_pre {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {G R U amp : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W : Devm → Prop} {T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (ha : Abstracts σ s) (hlock : σ.get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : σ.get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0)
    (hsup : SupplyOkAt sevm W W (σ.get tokenSlot) T U 0x17c 0x1c0) (hT0 : T ≠ 0)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hG : 60000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (Aw : B256), Aw.toNat = amp →
      ExLive sevm W b1 (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x380 →
      WordAt img1 0x140 T → WordAt img1 0x1e0 (cwFee (σ.get feeSlot)) →
      WordAt img1 0x200 (σ.get adminFeeSlot) → WordAt img1 0x220 Aw →
      WordAt img1 0x280 (balAt σ 0) → WordAt img1 0x2a0 (balAt σ 1) →
      WordAt img1 0x2c0 (balAt σ 2) → WordAt img1 0x2e0 (balAt σ 0) →
      WordAt img1 0x300 (balAt σ 1) → WordAt img1 0x320 (balAt σ 2) →
      WordAt img1 0x360 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b1 [] M1 g) t_31b7_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_304f_c0 Q := by
  have hWc := hL.wc
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3 := ⟨G - 3, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 23 := ⟨g2 - 23, by omega⟩
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hv2, lockSlot_lit, hlock]; decide) ·)
  -- tree t_305d_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g4 b4 hb4 hg41 hg42; replace hL := hL.sstoreE hb4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 22 := ⟨g4 - 22, by omega⟩
  xr (rx_callvalue (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  -- tree t_306f_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g6 b6 v6 hb6 hv6 hg61 hg62; replace hv6 := hL.val hv6; replace hL := hL.sloadE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 59 := ⟨g6 - 59, by omega⟩
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hv6, isKilledSlot_lit, Stor.get_set_ne _ (by decide) _, hkill]; decide) ·)
  -- tree t_307c_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x160) (c := 21) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc0 0x160 32 = 0x180 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g8 b8 v8 hb8 hv8 hg81 hg82; replace hv8 := hL.val hv8; replace hL := hL.sloadE hb8
  rw [show Bytes.toB256 [5] = tokenSlot by decide, Stor.get_set_ne _ (by decide) _] at hv8; subst hv8
  obtain ⟨g9, rfl⟩ : ∃ g, g8 = g + 2 := ⟨g8 - 2, by omega⟩
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [1, 124] = (0x17c : B256) by decide, show Bytes.toB256 [4] = (4 : B256) by decide,
    show Bytes.toB256 [1, 192] = (0x1c0 : B256) by decide, show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read (0x17c : B256).toNat (4 : B256).toNat).1 = totalSupplyData := by
    rw [hR.read, show (0x17c : B256).toNat = 0x17c by decide, show (4 : B256).toNat = 4 by decide,
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  refine rxe_staticWord (o := 0x1c0) (s := 0x1e0) hL hWc hsup (by omega) (by omega) hin hR hW rfl
    (by show memExtsSize M.size _ = _; rw [hsz]; decide) (by decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA' hrd hgd1 hgd2
  clear hR hW hsz hin hL
  have hR := hR'; have hW := hW'; have hsz := hsz'; have hL := hLd; clear hR' hW' hsz' hLd
  obtain ⟨g10, hg10⟩ : ∃ g, d.gasLeft = g + 82 := ⟨d.gasLeft - 82, by omega⟩
  rw [hg10]
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_309d_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_returndatasize (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hrd]; exact ex_rds_gt hlen hlt) ·)
  -- tree t_30aa_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hrs) ·)
  rw [ex_ans_read _ _ _ hlen, hA']
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1e0 0x140 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_xor rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [zero_lit, B256.xor_zero]; exact hT0) ·)
  -- tree t_30c5_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g11 b11 v11 hb11 hv11 hg111 hg112; replace hv11 := hL.val hv11; replace hL := hL.sloadE hb11
  rw [show Bytes.toB256 [2] = feeSlot by decide, Stor.get_set_ne _ (by decide) _] at hv11; subst hv11
  obtain ⟨g12, rfl⟩ : ∃ g, g11 = g + 125 := ⟨g11 - 125, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_mulGuard hmf) ·)
  -- tree t_30de_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_30f2_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1e0 0x1e0 32 = 0x200 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g13 b13 v13 hb13 hv13 hg131 hg132; replace hv13 := hL.val hv13; replace hL := hL.sloadE hb13
  rw [show Bytes.toB256 [3] = adminFeeSlot by decide, Stor.get_set_ne _ (by decide) _] at hv13; subst hv13
  obtain ⟨g14, rfl⟩ : ∃ g, g13 = g + 60 := ⟨g13 - 60, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x200) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x200 32 = 0x220 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x160) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x180) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x200) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mloadX (o := 0x220) (c := 6) hR hW hsz rfl (by decide) (by hrs) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x220 0x220 32 = 0x240 by decide] at hsz
  have ha' : Abstracts (b13.getStor sevm.currentTarget) s := ha.of_lock fun x hx => by
    rw [hL.stor x]; exact Stor.get_set_ne _ (by rw [lockSlot_lit]; exact Ne.symm hx) _
  have haG := aGas_le sevm b13
  obtain ⟨g15, hg15⟩ : ∃ g, g14 = g + aGas sevm b13 + 19 := ⟨g14 - aGas sevm b13 - 19, by omega⟩
  rw [hg15]
  obtain ⟨w, ⟨M', hrun, -, hW', hsz'⟩, hw⟩ := a_exact (G := g15)
    (ret := Nat.toB256 (0x3126 + 6)) (S := _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: []) hfork ha' hA hW
    hsz (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
  refine rxe_pcCall rli_prog_27 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    hrun ?_
  replace hL := hL.aBaseE
  clear hR hW hsz hrun
  have hR := Mem.reads_data M'
  have hW := hW'
  have hsz := hsz'
  clear hW' hsz'
  obtain ⟨g16, rfl⟩ : ∃ g, g15 = g + 130 := ⟨g15 - 130, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x260) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x260 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x220) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x220 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x200) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x200 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x1e0 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x1c0 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x1a0 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x180 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x160 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x140 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x260) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x220) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x220 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0xc0 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g17 b17 v17 hb17 hv17 hg36 hg37; replace hv17 := hL.val hv17; replace hL := hL.sloadE hb17
  obtain ⟨g18, rfl⟩ : ∃ g, g17 = g + 66 := ⟨g17 - 66, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x280) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x280 0x280 32 = 0x2a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x2a0 0xc0 32 = 0x2a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g19 b19 v19 hb19 hv19 hg56 hg57; replace hv19 := hL.val hv19; replace hL := hL.sloadE hb19
  obtain ⟨g20, rfl⟩ : ∃ g, g19 = g + 72 := ⟨g19 - 72, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x2a0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x2a0 0x2a0 32 = 0x2c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x2c0 0xc0 32 = 0x2c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g21 b21 v21 hb21 hv21 hg76 hg77; replace hv21 := hL.val hv21; replace hL := hL.sloadE hb21
  obtain ⟨g22, rfl⟩ : ∃ g, g21 = g + 114 := ⟨g21 - 114, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x2c0) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x2c0 0x2c0 32 = 0x2e0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x280) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x2e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x2e0 0x2e0 32 = 0x300 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz (cw_off (by decide) (by decide)) (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x300) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x300 0x300 32 = 0x320 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz (cw_off (by decide) (by decide)) (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x320) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x320 0x320 32 = 0x340 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x360) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x340 0x360 32 = 0x380 by decide] at hsz
  have e17 : v17 = balAt σ 0 := by
    rw [hv17, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  have e19 : v19 = balAt σ 1 := by
    rw [hv19, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  have e21 : v21 = balAt σ 2 := by
    rw [hv21, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  subst e17 e19 e21
  exact k _ M _ g22 w hw hL hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega)

end Blanc.Lift.Curve3Pool
