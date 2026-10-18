import Blanc.Lift.Curve3Pool.Walk.RliLiveFront
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPre

/-!
# `add_liquidity`, forward: the dispatcher, the guards, `_A`, the supply and the balances

`rx_dispatch_al`: with the `add_liquidity` selector the frame's entry tree runs to the arm's body
`t_0e55_c0`. `rx_al_pre` (`t_0e55_c0` → the supply test): the lock, no value, the pool alive,
`fees` zeroed at `0x140 … 0x180`, the adjusted fee `fee · 3 / 8` (checked) at `0x1a0`,
`admin_fee` at `0x1c0`, `_A` (`a_exact`) at `0x1e0`, 3Crv's `totalSupply()` (`SupplyOkAt`,
window `0x27c`/`0x2c0`) at `0x240`, `D0 = 0` at `0x2e0` and the balances at `0x300 … 0x340`; then
the supply test: `T = 0` runs on at `t_1031_c4`, `T ≠ 0` at `t_0f8f_c0` (`D0`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The dispatcher, forward** (`add_liquidity`). -/
theorem rx_dispatch_al {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_0e55_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + 315)) t_0000_c0 Q := by
  have hR0 := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hsz0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hX : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD 0 32 0) = 0x4515cef3 := by
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
  xr (rx_branch_zero' (by rw [hX]; decide) ·)
  exact k

theorem al_prog_27 : cert.prog[27]? = some t_00a9_c27 := prog_27

/-- The supply test falls through on a positive supply. -/
theorem al_supply_test {T : B256} (hT : T ≠ 0) :
    B256.eqCheck (B256.gtCheck T (Bytes.toB256 [0])) 0 = 0 := by
  have hgt : B256.gtCheck T (Bytes.toB256 [0]) ≠ 0 := by
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0]).toNat = 0 by decide]
    exact Nat.pos_of_ne_zero fun h => hT (B256.toNat_inj _ _ (by rw [h]; rfl))
  by_contra h
  exact hgt (eqCheck_ne_zero_eq h)

/-- **The guards, `_A`, the supply and the balances, forward** (`t_0e55_c0` → the supply
test). -/
theorem rx_al_pre {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {G R U amp : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W : Devm → Prop} {T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcd : sevm.data.length < 2 ^ 256)
    (hL : ExLive sevm W b σ) (ha : Abstracts σ s) (hlock : σ.get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : σ.get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0)
    (hsup : SupplyOkAt sevm W W (σ.get tokenSlot) T U 0x27c 0x2c0)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hG : 60000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (Aw : B256), Aw.toNat = amp →
      ExLive sevm W b1 (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x360 →
      WordAt img1 0x140 0 → WordAt img1 0x160 0 → WordAt img1 0x180 0 →
      WordAt img1 0x1a0 (cwFee (σ.get feeSlot)) → WordAt img1 0x1c0 (σ.get adminFeeSlot) →
      WordAt img1 0x1e0 Aw → WordAt img1 0x240 T → WordAt img1 0x2e0 0 →
      WordAt img1 0x300 (balAt σ 0) → WordAt img1 0x320 (balAt σ 1) →
      WordAt img1 0x340 (balAt σ 2) → R ≤ g → g ≤ G →
      (T = 0 → SFunc.RunEx cert.prog sevm (St b1 [] M1 g) t_1031_c4 Q) ∧
      (T ≠ 0 → SFunc.RunEx cert.prog sevm (St b1 [] M1 g) t_0f8f_c0 Q)) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_0e55_c0 Q := by
  have hWc := hL.wc
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3 := ⟨G - 3, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 23 := ⟨g2 - 23, by omega⟩
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hv2, lockSlot_lit, hlock]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g4 b4 hb4 hg41 hg42; replace hL := hL.sstoreE hb4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 22 := ⟨g4 - 22, by omega⟩
  xr (rx_callvalue (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g6 b6 v6 hb6 hv6 hg61 hg62; replace hv6 := hL.val hv6; replace hL := hL.sloadE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 61 := ⟨g6 - 61, by omega⟩
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hv6, isKilledSlot_lit, Stor.get_set_ne _ (by decide) _, hkill]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldatasize (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_calldatacopy (o := 0x140) (z := 0x60) (c := 33) hR hW hsz (by decide) (by decide) (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc0 0x140 0x60 = 0x1a0 by decide] at hsz
  rw [B256.toNat_toB256_of_lt hcd, sliceD_data_end] at hR
  have z0 : WordAt (Bytes.writeAt img 0x140 (List.replicate 0x60 0)) 0x140 0 := al_zeroWord img (j := 0) (by omega)
  have z1 : WordAt (Bytes.writeAt img 0x140 (List.replicate 0x60 0)) 0x160 0 := al_zeroWord img (j := 1) (by omega)
  have z2 : WordAt (Bytes.writeAt img 0x140 (List.replicate 0x60 0)) 0x180 0 := al_zeroWord img (j := 2) (by omega)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g8 b8 v8 hb8 hv8 hg81 hg82; replace hv8 := hL.val hv8; replace hL := hL.sloadE hb8
  rw [show Bytes.toB256 [2] = feeSlot by decide, Stor.get_set_ne _ (by decide) _] at hv8; subst hv8
  obtain ⟨g9, rfl⟩ : ∃ g, g8 = g + 125 := ⟨g8 - 125, by omega⟩
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
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1a0 0x1a0 32 = 0x1c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g10 b10 v10 hb10 hv10 hg101 hg102; replace hv10 := hL.val hv10; replace hL := hL.sloadE hb10
  rw [show Bytes.toB256 [3] = adminFeeSlot by decide, Stor.get_set_ne _ (by decide) _] at hv10; subst hv10
  obtain ⟨g11, rfl⟩ : ∃ g, g10 = g + 48 := ⟨g10 - 48, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1c0 0x1c0 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x140) (v := 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH z0) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x160) (v := 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH z1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x180) (v := 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH z2) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mloadX (o := 0x1e0) (c := 6) hR hW hsz rfl (by decide) (by hrs) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x1e0 0x1e0 32 = 0x200 by decide] at hsz
  -- `_A`
  have ha' : Abstracts (b10.getStor sevm.currentTarget) s := ha.of_lock fun x hx => by
    rw [hL.stor x]; exact Stor.get_set_ne _ (by rw [lockSlot_lit]; exact Ne.symm hx) _
  have haG := aGas_le sevm b10
  obtain ⟨g12, hg12⟩ : ∃ g, g11 = g + aGas sevm b10 + 19 := ⟨g11 - aGas sevm b10 - 19, by omega⟩
  rw [hg12]
  obtain ⟨w, ⟨M', hrun, -, hW', hsz'⟩, hw⟩ := a_exact (G := g12)
    (ret := Nat.toB256 (0xee2 + 6)) (S := _ :: _ :: _ :: _ :: _ :: _ :: []) hfork ha' hA hW
    hsz (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
  refine rxe_pcCall al_prog_27 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    hrun ?_
  replace hL := hL.aBaseE
  clear hR hW hsz hrun
  have hR := Mem.reads_data M'
  have hW := hW'
  have hsz := hsz'
  clear hW' hsz'
  obtain ⟨p1, rfl⟩ : ∃ g, g12 = g + 91 := ⟨g12 - 91, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x220) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x200 0x220 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x1e0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x1c0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x1a0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x180 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x160 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x140 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x220) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x1e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x1e0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x260) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x240 0x260 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro p2 c2 u2 hc2 hu2 hp21 hp22; replace hu2 := hL.val hu2; replace hL := hL.sloadE hc2
  obtain ⟨p3, rfl⟩ : ∃ g, p2 = g + 2 := ⟨p2 - 2, by omega⟩
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [5] = tokenSlot by decide, Stor.get_set_ne _ (by decide) _] at hu2; subst hu2
  rw [show Bytes.toB256 [2, 124] = (0x27c : B256) by decide, show Bytes.toB256 [4] = (4 : B256) by decide,
    show Bytes.toB256 [2, 192] = (0x2c0 : B256) by decide, show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read (0x27c : B256).toNat (4 : B256).toNat).1 = totalSupplyData := by
    rw [hR.read, show (0x27c : B256).toNat = 0x27c by decide, show (4 : B256).toNat = 4 by decide,
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  refine rxe_staticWord (o := 0x2c0) (s := 0x2e0) hL hWc hsup (by omega) (by omega) hin hR hW rfl
    (by show memExtsSize M.size _ = _; rw [hsz]; decide) (by decide) ?_
  intro d M' out hLd hR' hW' hsz' hlen hlt hA' hrd hgd1 hgd2
  clear hR hW hsz hin hL
  have hR := hR'; have hW := hW'; have hsz := hsz'; have hL := hLd; clear hR' hW' hsz' hLd
  obtain ⟨p4, hp4⟩ : ∃ g, d.gasLeft = g + 122 := ⟨d.gasLeft - 122, by omega⟩
  rw [hp4]
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
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hrs) ·)
  rw [ex_ans_read _ _ _ hlen, hA']
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x240) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x2e0 0x240 32 = 0x2e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x2e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x2e0 0x2e0 32 = 0x300 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x300 0xc0 32 = 0x300 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro p5 c5 u5 hc5 hu5 hp51 hp52; replace hu5 := hL.val hu5; replace hL := hL.sloadE hc5
  obtain ⟨p6, rfl⟩ : ∃ g, p5 = g + 66 := ⟨p5 - 66, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x300) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x300 0x300 32 = 0x320 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x320 0xc0 32 = 0x320 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro p7 c7 u7 hc7 hu7 hp71 hp72; replace hu7 := hL.val hu7; replace hL := hL.sloadE hc7
  obtain ⟨p8, rfl⟩ : ∃ g, p7 = g + 72 := ⟨p7 - 72, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x320) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x320 0x320 32 = 0x340 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x340 0xc0 32 = 0x340 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro p9 c9 u9 hc9 hu9 hp91 hp92; replace hu9 := hL.val hu9; replace hL := hL.sloadE hc9
  obtain ⟨p10, rfl⟩ : ∃ g, p9 = g + 47 := ⟨p9 - 47, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x340) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x340 0x340 32 = 0x360 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x240) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  have e5 : u5 = balAt σ 0 := by
    rw [hu5, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  have e7 : u7 = balAt σ 1 := by
    rw [hu7, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  have e9 : u9 = balAt σ 2 := by
    rw [hu9, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  subst e5 e7 e9
  have hk := k c9 M _ p10 w hw hL hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega)
  by_cases hT : T = 0
  · subst hT
    xr (rx_branchTo_succ (by decide) (g := t_1031_c4) rfl ·)
    exact hk.1 rfl
  · xr (rx_branchTo_zero' (al_supply_test hT) ·)
    exact hk.2 hT

end Blanc.Lift.Curve3Pool
