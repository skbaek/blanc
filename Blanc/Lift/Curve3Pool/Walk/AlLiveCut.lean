import Blanc.Lift.FrameWalkCut
import Blanc.Lift.Curve3Pool.Walk.AlLiveFront
import Blanc.Lift.Curve3Pool.Bridge

/-!
# `add_liquidity`, forward to its supply call, cut

`rx_al_toSupply`: the frame's entry tree cut (`SFunc.cutPath`) at its first external
instruction, the `totalSupply()` `STATICCALL` (`alSupplyPath`, which crosses the internal `_A()`
call and its return-address `PC`), runs from the frame's start to the call site: a state whose
world satisfies `W`, whose stack holds the call's operands (all the gas, the stored token, the
window `0x27c`/`4`/`0x2c0`/`0x20`), whose gas covers `U` and whose input window holds
`totalSupply()`'s calldata. With `xa_cutAt_start` this puts the frame's actual derivation at that
state (`AddLiquidityLive`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The steps from the entry tree to `add_liquidity`'s supply call. -/
def alSupplyPath : List CutStep :=
  [.nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx,
  .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s,
  .ds, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx,
  .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx,
  .nx, .nx, .nx, .nx, .nx, .z, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s,
  .ds, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx,
  .nx, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx,
  .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx,
  .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .pc, .nx, .nx, .cl, .ds, .nx, .nx, .nx, .nx, .nx,
  .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx,
  .nx, .nx, .nx, .nx]

theorem alSupplyPath_ok : SFunc.cutPathOk cert.prog aEntries alSupplyPath t_0000_c0 = true := by
  decide

theorem a_noHaltSet : NoHaltSet cert.prog aEntries = true := by decide

/-- **The frame's start to its supply call, forward** (see the module note). -/
theorem rx_al_toSupply {sevm : Sevm} {pre : Devm} {s : State} {W : Devm → Prop} {G U amp : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hWb : W pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hG : 70000 + U ≤ G) (hGb : G < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty G)
      (SFunc.cutPath cert.prog alSupplyPath t_0000_c0)
      (fun r => ∃ (b : Devm) (S : List B256) (M : Mem) (g : Nat),
        r = .halted (St b (Nat.toB256 g :: (pre.getStor sevm.currentTarget).get tokenSlot ::
          0x27c :: 4 :: 0x2c0 :: 0x20 :: S) M g) ∧
        W b ∧ U ≤ g ∧ g < 2 ^ 256 ∧
        (M.read (0x27c : B256).toNat (4 : B256).toNat).1 = totalSupplyData ∧
        S.length < 1024) := by
  set σ := pre.getStor sevm.currentTarget with hσ
  obtain ⟨G, rfl⟩ : ∃ g, G = g + 315 := ⟨G - 315, by omega⟩
  unfold alSupplyPath
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
  have hL : ExLive sevm W pre σ := ⟨fun _ => rfl, hid, hWc, hWb⟩
  have hR := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hW := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have hsz := vyMem_empty_size (Sevm.dataWord sevm 0)
  clear hR0 hsz0
  generalize vyMem Mem.empty (Sevm.dataWord sevm 0) = M at hR hW hsz
  generalize vyImg [] (Sevm.dataWord sevm 0) = img at hR
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
  exact ⟨_, .last rfl, _, _, _, _, rfl, hL.w, by omega, by omega, hin,
    by simp only [List.length_nil]; omega⟩

end Blanc.Lift.Curve3Pool
