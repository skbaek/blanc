import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveP2

/-!
# `remove_liquidity_one_coin`, forward: the dispatcher and the guards

`rx_dispatch_oc`: with the `remove_liquidity_one_coin` selector the frame's entry tree runs to the
arm's body `t_440c_c0`. `rx_oc_pre` (`t_440c_c0` → the call idiom of `_calc_withdraw_one_coin`):
the lock clear and set, no value, the `int128` clamps of `i`, the pool alive, and the arguments
staged.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The dispatcher, forward** (`remove_liquidity_one_coin`). -/
theorem rx_dispatch_oc {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_440c_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + 578)) t_0000_c0 Q := by
  have hR0 := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hsz0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hX : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD 0 32 0) = 0x1a4d01d2 := by
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

/-- The base the guards leave: the lock read and set, `is_killed` read. -/
def ocPreBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
    (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])

/-- The guards' charge: `233` for their instructions, the lock read and set, `is_killed` read. -/
def ocPreCost (sevm : Sevm) (b : Devm) : Nat :=
  233 + sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])

/-- The memory the guards leave: two zero frame words, `_token_amount` and `i` staged. -/
def ocPreMem (sevm : Sevm) (M : Mem) : Mem :=
  (((M.write 0x140 (Bytes.toB256 [0]).toBytes).write 0x160 (Bytes.toB256 [0]).toBytes).write 0x1a0
    (Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes).write 0x1c0
    (Sevm.dataWord sevm (Bytes.toB256 [36])).toBytes

/-- **The guards and the arguments, forward, exactly** (core). -/
theorem rx_oc_preE {sevm : Sevm} {b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hL : ExLive sevm W b σ) (hlock : σ.get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : σ.get isKilledSlot = 0) (hi3 : (ocI sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0) (hcl : VyClamps img)
    (hG : 26600 + R ≤ G)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat),
      ExLive sevm W b1 (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x1e0 → R ≤ g → g ≤ G →
      G = g + ocPreCost sevm b → b1 = ocPreBase sevm b → M1 = ocPreMem sevm M →
      SFunc.RunEx cert.prog sevm
        (St b1 [ocAmt sevm, ocI sevm, Bytes.toB256 [0], Bytes.toB256 [0]] M1 g)
        (pcCallTree 0x448b 0x3c 0xca 36 t_4491_c0) Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_440c_c0 Q := by
  have e40 : Bytes.toB256 (img.sliceD 64 32 0) = Bytes.toB256 vyC40 := by
    rw [hcl.2.1, B256.toB256_toBytes]
  have e60 : Bytes.toB256 (img.sliceD 96 32 0) = Bytes.toB256 vyC60 := by
    rw [hcl.2.2.1, B256.toB256_toBytes]
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3 := ⟨G - 3, by omega⟩
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 23 := ⟨g2 - 23, by omega⟩
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hv2, lockSlot_lit, hlock]; decide) ·)
  -- tree t_441a_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g4 b4 hb4 hg41 hg42 g4x; replace hL := hL.sstoreE hb4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 97 := ⟨g4 - 97, by omega⟩
  xr (rx_callvalue (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  -- tree t_442c_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x60) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x40) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_swap1 ·)
  xr (rx_sgt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [e40]; exact ex_clamp_hi hi3) ·)
  -- tree t_4442_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_swap2 ·)
  xr (rx_swap1 ·)
  xr (rx_slt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [e60]; exact ex_clamp_lo hi3) ·)
  -- tree t_4450_c0
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g6 b6 v6 hb6 hv6 hg61 hg62 g6x; replace hv6 := hL.val hv6; replace hL := hL.sloadE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 110 := ⟨g6 - 110, by omega⟩
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hv6, isKilledSlot_lit, Stor.get_set_ne _ (by decide) _, hkill]; decide) ·)
  -- tree t_445e_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x140) (c := 18) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mf1; intro M hMf1 hR hW hsz; rw [show memExtSize 0xc0 0x140 32 = 0x160 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x160) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mf2; intro M hMf2 hR hW hsz; rw [show memExtSize 0x160 0x160 32 = 0x180 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x160) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1a0) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mf3; intro M hMf3 hR hW hsz; rw [show memExtSize 0x180 0x1a0 32 = 0x1c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mf4; intro M hMf4 hR hW hsz; rw [show memExtSize 0x1c0 0x1c0 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  exact k _ M _ _ hL hR hW hsz (by omega) (by omega)
    (by unfold ocPreCost; rw [← hb2, ← hb4]; omega) (by rw [hb6, hb4, hb2]; rfl)
    (by rw [hMf4, hMf3, hMf2, hMf1]; rfl)


/-- **The guards and the arguments, forward** (`t_440c_c0` → the call idiom at `0x448b`). -/
theorem rx_oc_pre {sevm : Sevm} {b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hL : ExLive sevm W b σ) (hlock : σ.get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : σ.get isKilledSlot = 0) (hi3 : (ocI sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0) (hcl : VyClamps img)
    (hG : 26600 + R ≤ G)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (v1 v2 : B256),
      ExLive sevm W b1 (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x1e0 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b1 [ocAmt sevm, ocI sevm, v1, v2] M1 g)
        (pcCallTree 0x448b 0x3c 0xca 36 t_4491_c0) Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_440c_c0 Q :=
  rx_oc_preE hfork hstatic hL hlock hval hkill hi3 hR hW hsz hcl hG
    fun b1 M1 img1 g h1 h2 h3 h4 h5 h6 _ _ _ => k b1 M1 img1 g _ _ h1 h2 h3 h4 h5 h6

end Blanc.Lift.Curve3Pool
