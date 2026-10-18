import Blanc.Lift.FrameWalkCut
import Blanc.Lift.Curve3Pool.Walk.RliLiveFront

/-!
# `remove_liquidity_imbalance`, forward to its supply call, cut

`rx_rli_toSupply`: the frame's entry tree cut (`SFunc.cutPath`) at its first external
instruction, the `totalSupply()` `STATICCALL` (`rliSupplyPath`), runs from the frame's start to
the call site: a state whose world satisfies `W`, whose stack holds the call's operands (all the
gas, the stored token, the window `0x17c`/`4`/`0x1c0`/`0x20`), whose gas covers `U` and whose
input window holds `totalSupply()`'s calldata. With `xa_cutAt_start` this puts the frame's actual
derivation at that state (`RemoveImbalanceLive`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The steps from the entry tree to `remove_liquidity_imbalance`'s supply call. -/
def rliSupplyPath : List CutStep :=
  [.nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx,
  .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx,
  .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .s,
  .ds, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx,
  .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx,
  .nx, .s, .ds, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds,
  .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds,
  .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .z, .nx,
  .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .s, .ds, .nx, .nx, .nx,
  .nx, .s, .ds, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx, .nx]

theorem rliSupplyPath_ok : SFunc.cutPathOk cert.prog [] rliSupplyPath t_0000_c0 = true := by
  decide

/-- **The frame's start to its supply call, forward** (see the module note). -/
theorem rx_rli_toSupply {sevm : Sevm} {pre : Devm} {W : Devm → Prop} {G U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hWb : W pre)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hG : 61000 + U ≤ G) (hGb : G < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty G)
      (SFunc.cutPath cert.prog rliSupplyPath t_0000_c0)
      (fun r => ∃ (b : Devm) (S : List B256) (M : Mem) (g : Nat),
        r = .halted (St b (Nat.toB256 g :: (pre.getStor sevm.currentTarget).get tokenSlot ::
          0x17c :: 4 :: 0x1c0 :: 0x20 :: S) M g) ∧
        W b ∧ U ≤ g ∧ g < 2 ^ 256 ∧ (M.read (0x17c : B256).toNat (4 : B256).toNat).1 = totalSupplyData ∧
        S.length < 1024) := by
  set σ := pre.getStor sevm.currentTarget with hσ
  obtain ⟨G, rfl⟩ : ∃ g, G = g + 480 := ⟨G - 480, by omega⟩
  unfold rliSupplyPath
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
  exact ⟨_, .last rfl, _, _, _, _, rfl, hL.w, by omega, by omega, hin, by decide⟩

end Blanc.Lift.Curve3Pool
