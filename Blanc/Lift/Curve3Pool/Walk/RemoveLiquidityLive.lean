import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquiditySafe

/-!
# `remove_liquidity`, forward: an exact run from the frame's entry

The liveness walk builds `SFunc.RunEx` over the certificate's trees, read forwards: the
dispatcher (`rx_dispatch_rl`), the guarded prologue with the `totalSupply` call
(`rx_rl_pre`), the loop (`rx_rl_iter`), and the burn, event and lock clear (`rx_rl_post`).
Each segment is continuation-passing: it builds the run of its tree from the run of the rest.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The dispatcher, forward**: with the `remove_liquidity` selector, the frame's entry tree
runs to the arm's body `t_2c68_c0` over the prologue's memory, at 451 gas. -/
theorem rx_dispatch_rl {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_2c68_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + 451)) t_0000_c0 Q := by
  have hR0 := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hsz0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hX : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD 0 32 0) = 0xecb586a5 := by
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
  xr (rx_eq (v := 1) (by rw [hX]; decide) (by hr) ·)
  xr (rx_iszero (v := 0) (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_zero ·)
  exact k

theorem gtCheck_ne_zero_of_lt {x y : B256} (h : y < x) : B256.gtCheck x y ≠ 0 := by
  unfold B256.gtCheck
  simp only [gt_iff_lt, h, ↓reduceIte]
  decide

/-- `remove_liquidity`'s gas up to the `totalSupply` call (`Gs` is left at the call). -/
def rlPreCost (sevm : Sevm) (b : Devm) : Nat :=
  89 + sloadCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5])

/-- **The guarded prologue, forward** (`0x2c68` → the loop head): the lock is clear, no value,
`totalSupply` answers `T` (`SupplyOk`); the loop head runs over a base whose pool storage is the
entry's with the lock set, with `T` at `0x140`, zero amounts and fees, and counter `0`. -/
theorem rx_rl_pre {sevm : Sevm} {b : Devm} {Gs : Nat} {Q : Outcome → Prop} {W : Devm → Prop}
    {U : Nat} {T : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hcd : sevm.data.length < 2 ^ 256)
    (hlock : (b.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hWc : WClosed sevm W) (hWb : W b)
    (hsup : SupplyOk sevm W ((b.getStor sevm.currentTarget).get tokenSlot) T U)
    (hGs : U + 135 ≤ Gs) (hGs2 : 2300 < Gs) (hGs' : Gs < 2 ^ 256)
    (k : ∀ b1 M1 img1 G1, W b1 → (IdReady sevm b → IdReady sevm b1) →
      (∀ x, (b1.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) →
      b1.logs = b.logs → b1.output = b.output →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x2c0 → LoopImg img1 0 T (fun _ => 0) →
      Gs ≤ G1 + U + 135 →
      SFunc.RunEx cert.prog sevm (St b1 [3, 0x2a0] M1 G1) t_2cdb_c0 Q) :
    SFunc.RunEx cert.prog sevm
      (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) (Gs + rlPreCost sevm b)) t_2c68_c0 Q := by
  have hR := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hW := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have hsz := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hlk : B256.eqCheck (b.getStorVal sevm.currentTarget (Bytes.toB256 [0xff, 0xff, 0xff])) 0 ≠
      0 := by
    rw [getStorVal_eq, lockSlot_lit, hlock]; decide
  unfold rlPreCost
  rw [show Gs + (89 + sloadCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5])) =
    Gs + 2 + sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5]) + 3 + 3 + 21 + 3 +
      3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b
      (Bytes.toB256 [0xff, 0xff, 0xff])) (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) + 3 +
      3 + 1 + 10 + 3 + 3 + sloadCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) + 3 by omega]
  xr (rx_push rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlk ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ·)
  xr (rx_callvalue (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x160) (c := 21) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  xr (rx_gas (by hr) ·)
  have htokv : (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])).getStorVal sevm.currentTarget
      (Bytes.toB256 [5]) = (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [lockSlot_lit, tokenSlot_lit, getStorVal_afterSstore_ne lock_ne_token, getStorVal_afterSload]
    rfl
  rw [htokv, show Bytes.toB256 [1, 124] = 0x17c by decide, show Bytes.toB256 [4] = 4 by decide,
    show Bytes.toB256 [1, 192] = 0x1c0 by decide, show Bytes.toB256 [32] = 0x20 by decide]
  have hWb2 : W (afterSload sevm (afterSstore sevm (afterSload sevm b
      (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
      (Bytes.toB256 [5])) := hWc.sload _ _ (hWc.sstore _ _ _ (hWc.sload _ _ hWb))
  have hin : (M.read 0x17c 4).1 = totalSupplyData := by
    rw [hR.read, Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  obtain ⟨d, out, hrun, hpost, hlen32, hlt, hT, hgas, hgle, hWd, hidd⟩ :=
    hsup _ [] M Gs hWb2 (by omega) hGs' hin
  xr (.next hrun ·)
  have hd := hpost.eq_St
  rw [show (0x17c : B256).toNat = 0x17c by decide, show (4 : B256).toNat = 4 by decide,
    show (0x1c0 : B256).toNat = 0x1c0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hd
  rw [hd]
  obtain ⟨G1, hG1⟩ : ∃ G1, d.gasLeft = G1 + 135 := ⟨d.gasLeft - 135, by omega⟩
  rw [hG1]
  have hrds : B256.gtCheck d.returnData.length.toB256 (Bytes.toB256 [0x1f]) ≠ 0 := by
    rw [hpost.returnData]
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  have hW1 := (hW.extends [(0x17c, 4), (0x1c0, 0x20)]).write 0x1c0 (out.take 0x20)
  replace hR := (hR.extends [(0x17c, 4), (0x1c0, 0x20)]).write (hW.extends _) 0x1c0 (out.take 0x20)
  have hext : (M.extends [(0x17c, 4), (0x1c0, 0x20)]).size = 0x1e0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  replace hsz : ((M.extends [(0x17c, 4), (0x1c0, 0x20)]).write 0x1c0 (out.take 0x20)).size =
      0x1e0 := by
    rw [Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  replace hW := hW1
  clear hW1
  have hT1 : Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 352
      (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (out.take 32)).sliceD 448 32 0) = T := by
    have h := Bytes.sliceD_writeAt (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 352
      (Bytes.toB256 [24, 22, 13, 221]).toBytes) (out.take 32) 448
    rw [List.length_take, Nat.min_eq_left hlen32] at h
    rw [h, hT]
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_returndatasize (by hr) ·)
  xr (rx_gt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hrds ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ·)
  rw [hT1]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldatasize (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_calldatacopy (o := 0x1e0) (z := 0x60) (c := 21) hR hW hsz rfl rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldatasize (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_calldatacopy (o := 0x240) (z := 0x60) (c := 21) hR hW hsz rfl rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  refine rxe_mstore (o := 0x2a0) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_add (by hr) ·)
  rw [show [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [2, 160]] = ([3, 0x2a0] : List B256)
    by decide]
  have hZ : List.sliceD sevm.data (Nat.toB256 (List.length sevm.data)).toNat 96 0 =
      List.replicate 96 0 := by
    rw [B256.toNat_toB256_of_lt hcd]; exact List.sliceD_length_eq
  refine k _ _ _ _ hWd (fun hid => hidd (((hid.afterSload _).afterSstore _ _).afterSload _))
    (fun x => ?_) ?_ ?_ hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ (by omega)
  · rw [hpost.stor, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor, lockSlot_lit]
    rfl
  · rw [hpost.logs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [hpost.output rfl, afterSload_output, afterSstore_output, afterSload_output]
  · rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]
    exact WordAt.write_self _ _ _
  · rw [hZ]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_self _ _ _)
      (.inl (by decide))) (.inl (by decide))) (.inl (by decide))
  · rw [hZ]
    intro j hj
    refine WordAt.write_other ?_ (.inl (by omega))
    by_cases hj3 : j < 3
    · refine WordAt.write_other ?_ (.inl (by omega))
      unfold WordAt
      rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]; omega),
        List.sliceD_replicate_zero]
      decide
    · unfold WordAt
      rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]; omega),
        List.sliceD_replicate_zero]
      decide

/-- `remove_liquidity`'s loop body up to `0x2e0c`, forward (variant A: loop head t_2cdb_c0,
memory size 0x2c0). -/
theorem rx_rl_s1A {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T B : B256} {a : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2c0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0) (hG : 2300 < Gc)
    (k : ∀ M' img', Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x380 → LoopImg img' i T a →
      WordAt img' 0x2c0 (B * rlAmt sevm / T) →
      SFunc.RunEx cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gc + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 7 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1)) t_2cdb_c0 Q := by
  have hctr := hL.ctr
  have hT := hL.supply
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  rw [hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_or rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hmulw ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hT.read]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hT0 ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x2c0) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x2e0) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x300) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x320) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x340) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x360) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hminw ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_afterSload, getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlew ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  refine k _ _ hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_
  · wchainT; exact hctr
  · wchainT; exact hT
  · intro j hj; wchainT; exact hL.amt j hj
  · wchainT

/-- `remove_liquidity`'s loop body up to `0x2e0c`, forward (variant B: loop head t_2cdb_c46,
memory size 0x5e0). -/
theorem rx_rl_s1B {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T B : B256} {a : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = B)
    (hmulw : (B256.eqCheck (B * rlAmt sevm / B) (rlAmt sevm) ||| B256.eqCheck B 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (B * rlAmt sevm / T) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck B (B * rlAmt sevm / T)) 0 ≠ 0) (hG : 2300 < Gc)
    (k : ∀ M' img', Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' i T a →
      WordAt img' 0x2c0 (B * rlAmt sevm / T) →
      SFunc.RunEx cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gc + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1)) t_2cdb_c46 Q := by
  have hctr := hL.ctr
  have hT := hL.supply
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  rw [hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_or rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hmulw ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hT.read]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hT0 ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x2c0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x2e0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x300) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x320) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x340) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x360) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hminw ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_afterSload, getStorVal_eq, hB]
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlew ·)
  xr (rx_dest ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  refine k _ _ hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_
  · wchainT; exact hctr
  · wchainT; exact hT
  · intro j hj; wchainT; exact hL.amt j hj
  · wchainT

/-- The `transfer` payload with its two identity copies, forward (variant A: memory 0x380). -/
theorem rx_rl_s2A {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x380) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 532 < 2 ^ 256)
    (k : ∀ b' M' img', BaseRel b b' → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x580 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunEx cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 532)) t_2e0c_c0 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x1e0 + 32 * i) (c := 3) hR hW hsz (off_amt hi)
    ⟨by rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩ ?_
  intro M hR hW hsz
  rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x400) (c := 19) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x420) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 5) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  have e1 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img1, hR, hI⟩ := e1
  have f_ctr : WordAt img1 0x2a0 (Nat.toB256 i) := by rw [hI]; wchainT; exact hL.ctr
  have f_T : WordAt img1 0x140 T := by rw [hI]; wchainT; exact hL.supply
  have f_v : WordAt img1 0x2c0 V := by rw [hI]; wchainT; exact hv
  have f_400 : WordAt img1 0x400 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0x420 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  have f_amt : ∀ j, j < 6 → WordAt img1 (0x1e0 + 32 * j) (Function.update a i V j) := by
    intro j hj
    rw [hI]
    by_cases e : j = i
    · subst e; rw [Function.update_self]; wchainT
    · rw [Function.update_of_ne e]; wchainT; exact hL.amt j hj
  clear hI hL hv
  refine rxe_identity (i := 0x420) (n := 4) (o := 0x480) (z := 4) (ext := 9) (X := 127) hid hdepth hR hW
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 4 = 18 by decide]; omega) (by omega) (by hr) ?_
  intro b2 M hsha hR hW hsz
  have hsel4 : (img1.sliceD 0x420 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_400.read]
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 1) rfl ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x484) (c := 6) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x4a4) (c := 6) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identity (i := 0x460) (n := 0x64) (o := 0x500) (z := 0x64) (ext := 16) (X := 143)
    (hid.of_rel hb12) hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 0x64 = 27 by decide]; omega) (by omega) (by hr) ?_
  intro b3 M hsha2 hR hW hsz
  rw [transfer_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2

  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  refine k b3 M img3 (hb12.trans hb23) hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_ _ _
  · rw [hI]; wchainT; exact f_ctr
  · rw [hI]; wchainT; exact f_T
  · intro j hj; rw [hI]; wchainT; exact f_amt j hj
  · rw [hI]; exact Region.write_self _ _ _

/-- The `transfer` payload with its two identity copies, forward (variant B: memory 0x5e0). -/
theorem rx_rl_s2B {sevm : Sevm} {b : Devm} {Gc : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 482 < 2 ^ 256)
    (k : ∀ b' M' img', BaseRel b b' → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunEx cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 482)) t_2e0c_c0 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x1e0 + 32 * i) (c := 3) hR hW hsz (off_amt hi)
    ⟨by rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩ ?_
  intro M hR hW hsz
  rw [memExtSize_of_le (by decide) (by omega)] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x400) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x420) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 5) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  have e1 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img1, hR, hI⟩ := e1
  have f_ctr : WordAt img1 0x2a0 (Nat.toB256 i) := by rw [hI]; wchainT; exact hL.ctr
  have f_T : WordAt img1 0x140 T := by rw [hI]; wchainT; exact hL.supply
  have f_v : WordAt img1 0x2c0 V := by rw [hI]; wchainT; exact hv
  have f_400 : WordAt img1 0x400 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0x420 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  have f_amt : ∀ j, j < 6 → WordAt img1 (0x1e0 + 32 * j) (Function.update a i V j) := by
    intro j hj
    rw [hI]
    by_cases e : j = i
    · subst e; rw [Function.update_self]; wchainT
    · rw [Function.update_of_ne e]; wchainT; exact hL.amt j hj
  clear hI hL hv
  refine rxe_identity (i := 0x420) (n := 4) (o := 0x480) (z := 4) (ext := 0) (X := 118) hid hdepth hR hW
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 4 = 18 by decide]; omega) (by omega) (by hr) ?_
  intro b2 M hsha hR hW hsz
  have hsel4 : (img1.sliceD 0x420 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_400.read]
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 1) rfl ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x484) (c := 3) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x4a4) (c := 3) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_swap (n := 0) rfl ·)
  xr (rx_pop ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hr) ·)
  rw [Bytes.readWord_writeAt_self]
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 2) rfl (by hr) ·)
  xr (rx_dup (n := 4) rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identity (i := 0x460) (n := 0x64) (o := 0x500) (z := 0x64) (ext := 0) (X := 127)
    (hid.of_rel hb12) hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 0x64 = 27 by decide]; omega) (by omega) (by hr) ?_
  intro b3 M hsha2 hR hW hsz
  rw [transfer_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2

  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  refine k b3 M img3 (hb12.trans hb23) hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_ _ _
  · rw [hI]; wchainT; exact f_ctr
  · rw [hI]; wchainT; exact f_T
  · intro j hj; rw [hI]; wchainT; exact f_amt j hj
  · rw [hI]; exact Region.write_self _ _ _

/-! ## The `transfer` call's `raw_call` tail -/

/-- The `raw_call` site of `remove_liquidity`'s transfer: length word at `0x5a0`, copy buffer at
`0x3a0`, and its eight jump targets. -/
def rlSite : VyRawSite := ⟨0x05, 0xa0, 0x03, 0xa0, 0x2e, 0xdf, 0x2e, 0xf0, 0x2e, 0xf2, 0x2f, 0x17,
  0x2f, 0x6a, 0x2f, 0x40, 0x2f, 0x4e, 0x2f, 0x69⟩

theorem rl_join : cert.prog[15]? =
    some (vyRawCallJoin rlSite t_2f13_c15 t_2f3c_c15 t_2f4a_c15 t_2f65_c15 t_2f6a_c15) := rfl

theorem rl_tail : (SFunc.next (.push [0x2e, 0xdf] (by decide)) (.branch t_2edb_c0 t_2edf_c0)) =
    vyRawCallTail rlSite 15 t_2edb_c0 t_2f13_c15 t_2f3c_c15 t_2f4a_c15 t_2f65_c15 t_2f6a_c15 := rfl

/-- `remove_liquidity`'s gas from `0x2ea7` to the `transfer` call. -/
def rlS3Cost (sevm : Sevm) (b : Devm) (i : Nat) : Nat :=
  108 + sloadCost sevm b (coinsBase + Nat.toB256 i)

/-- The loop's next tree: its exit after the last coin, its head otherwise. -/
def rlNext (i : Nat) : SFunc := if i + 1 = 3 then t_2f7b_c15 else t_2cdb_c46

/-- **The transfer call and its tail, forward** (`0x2ea7` → the loop's next tree): `coins[i]`,
the `CALL` answered by `CoinPushOk`, the `raw_call` success test (`rxc_vyRawCallTail`), and
`i += 1`. -/
theorem rx_rl_s3 {sevm : Sevm} {b : Devm} {Gx : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {s i : Nat} {T V C : B256} {a : Nat → B256} {W : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hdepth : sevm.depth ≠ 0)
    (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s) (hs : s = 0x580 ∨ s = 0x5e0)
    (hL : LoopImg img i T a)
    (hdata : Region img 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)))
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C)
    (hpush : CoinPushOk sevm W C V U) (hGx : U + 2000 ≤ Gx) (hGb : Gx + 1000 < 2 ^ 256)
    (k : ∀ b' M' img' G', W b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' (i + 1) T a →
      Gx ≤ G' + U + 600 →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G') (rlNext i) Q) :
    ∀ x y, SFunc.RunEx cert.prog sevm (St b (x :: y :: [3, 0x2a0]) M (Gx + rlS3Cost sevm b i))
      t_2ea7_c0 Q := by
  intro x y
  have hs32 : s % 32 = 0 := by rcases hs with rfl | rfl <;> decide
  have hs0 : 0x580 ≤ s := by rcases hs with rfl | rfl <;> decide
  unfold rlS3Cost
  rw [show Gx + (108 + sloadCost sevm b (coinsBase + Nat.toB256 i)) = Gx + 2 +
    sloadCost sevm b (coinsBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 +
    3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 1 by omega]
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x500) hR hsz rfl ⟨by omega, hs32⟩ (by hr) ·)
  rw [(Region.word hdata.left).read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl ⟨by omega, hs32⟩ (by hr) ·)
  rw [hL.ctr.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl
    ⟨by rw [memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl, hs32⟩ ?_
  intro M hR hW hsz
  rw [memExtSize_of_le hs32 (by omega)] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl ⟨by omega, hs32⟩ (by hr) (by decide) ·)
  rw [keccak_zero]
  xr (rx_add (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_eq, hC]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
      (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [5, 32] = (0x520 : B256) by decide,
    show Bytes.toB256 [5, 192] = (0x5c0 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read 0x520 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes := by
    rw [hR.read]
    exact Region.slice (Region.write_other hdata.right (by simp only [B256.length_toBytes]; omega))
      (by simp only [List.length_append, B256.length_toBytes]; rfl)
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd⟩ :=
    hpush _ [3, 0x2a0] M Gx (hWc.sload _ _ hWb) (by omega) (by omega) hin
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x520 : B256).toNat = 0x520 by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x5c0 : B256).toNat = 0x5c0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d (1 :: [3, 0x2a0]) d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, rl_tail]
  have hext : (M.extends [(0x520, 0x44), (0x5c0, 0x20)]).size = 0x5e0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; rcases hs with rfl | rfl <;> decide
  have hsz5 : d.memory.size = 0x5e0 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x5c0 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail (hidd (hid.afterSload _))
    hdepth (by decide) rl_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [rlSite.lh, rlSite.ll]).toNat + 32 = 0x5c0 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  clear hrun
  rw [show (Bytes.toB256 [rlSite.lh, rlSite.ll]).toNat = 0x5a0 by decide,
    show (Bytes.toB256 [rlSite.bh, rlSite.bl]).toNat = 0x3a0 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
        (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)).size = 0x5e0 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x5a0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x5e0 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  obtain ⟨G', hG'⟩ : ∃ G', G2 = G' + 45 := ⟨G2 - 45, by omega⟩
  rw [hG']
  have hctr6 : WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
      (min d.returnData.length 32 + 32) 0)) 0x2a0 (Nat.toB256 i) := by
    wchain; exact hL.ctr
  xr (fun h => rx_dest (rx_dest h))
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR6 hsz6 rfl ⟨by decide, by decide⟩ (by hr) ·)
  rw [hctr6.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  rw [succ_lit hi]
  xr (rx_dup (n := 0) rfl (by hr) ·)
  xr (rx_dup (n := 3) rfl (by hr) ·)
  refine rxe_mstore (o := 0x2a0) (c := 3) hR6 hW6 hsz6 rfl (by decide) ?_
  intro M7 hR7 hW7 hsz7
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  have hWb' : W b' := hWc.sha _ _ _ hsha hWd
  have hidb' : IdReady sevm b' := (hidd (hid.afterSload _)).of_rel
    ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  have hstb' : ∀ x, (b'.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x := by
    intro x; rw [hsha.stor, hstor, afterSload_getStor]
  have hLI : LoopImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
      (min d.returnData.length 32 + 32) 0)) 0x2a0 (Nat.toB256 (i + 1)).toBytes) (i + 1) T a :=
    ⟨WordAt.write_self _ _ _, by wchain; exact hL.supply,
      fun j hj => by wchain; exact hL.amt j hj⟩
  have hgas' : Gx ≤ G' + U + 600 := by omega
  have hsz7' : M7.size = 0x5e0 := by rw [hsz7]; decide
  rcases (show i + 1 = 3 ∨ i + 1 < 3 by omega) with h3 | h3
  · have hn : rlNext i = t_2f7b_c15 := by unfold rlNext; simp only [h3, ↓reduceIte]
    have e0 : B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 = 0 := by rw [h3]; decide
    rw [e0]
    xr (rx_branchTo_zero ·)
    have := k b' M7 _ G' hWb' hidb' hstb' hR7 hW7 hsz7' hLI hgas'
    rwa [hn] at this
  · have hn : rlNext i = t_2cdb_c46 := by unfold rlNext; simp only [show i + 1 ≠ 3 by omega, ↓reduceIte]
    xr (rx_branchTo_succ (by rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide)
      rfl ·)
    have := k b' M7 _ G' hWb' hidb' hstb' hR7 hW7 hsz7' hLI hgas'
    rwa [hn] at this

end Blanc.Lift.Curve3Pool

