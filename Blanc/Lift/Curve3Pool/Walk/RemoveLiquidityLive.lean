import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquiditySafe

/-!
# `remove_liquidity`, forward: an exact run from the frame's entry

The liveness walk builds `SFunc.RunExact` over the certificate's trees, read forwards: the
dispatcher (`rx_dispatch_rl`), the guarded prologue with the `totalSupply` call
(`rx_rl_pre`), the loop (`rx_rl_iter`), and the burn, event and lock clear (`rx_rl_post`).
Each segment is continuation-passing: it builds the run of its tree from the run of the rest.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The dispatcher, forward**: with the `remove_liquidity` selector, the frame's entry tree
runs to the arm's body `t_2c68_c0` over the prologue's memory, at 451 gas. -/
theorem rx_dispatch_rl {sevm : Sevm} {b : Devm} {G : Nat} {r : Outcome}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (k : SFunc.RunExact cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_2c68_c0 r) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 451)) t_0000_c0 r := by
  have hR0 := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hsz0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hX : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD 0 32 0) = 0xecb586a5 := by
    rw [vyImg_selector]; exact hsel
  have hlen4 : B256.eqCheck (B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [0x04]))
      0 ≠ 0 := by
    rw [ltCheck_eq_zero_of_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide
  refine rx_push rfl (by hr) ?_
  refine rx_calldatasize (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hlen4 ?_
  refine rx_dest ?_
  refine rx_vyPrologue (by simp only [List.length_nil]; omega) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hX]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hX]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hX]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hX]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hX]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hX]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hX]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ?_
  refine rx_eq (v := 1) (by rw [hX]; decide) (by hr) ?_
  refine rx_iszero (v := 0) (by decide) (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_zero ?_
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
theorem rx_rl_pre {sevm : Sevm} {b : Devm} {Gs : Nat} {r : Outcome} {W : Devm → Prop}
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
      SFunc.RunExact cert.prog sevm (St b1 [3, 0x2a0] M1 G1) t_2cdb_c0 r) :
    SFunc.RunExact cert.prog sevm
      (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) (Gs + rlPreCost sevm b)) t_2c68_c0 r := by
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
  refine rx_push rfl (by hr) ?_
  refine rx_sload_sel hfork (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hlk ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ?_
  refine rx_callvalue (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by rw [hval]; decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x160) (c := 21) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_sload_sel hfork (by hr) ?_
  refine rx_gas (by hr) ?_
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
  obtain ⟨d, out, hrun, hpost, hlen32, hlt, hT, hgas, hWd, hidd⟩ :=
    hsup _ [] M Gs hWb2 (by omega) hGs' hin
  refine .next hrun ?_
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
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_returndatasize (by hr) ?_
  refine rx_gt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hrds ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ?_
  rw [hT1]
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_calldatasize (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_calldatacopy (o := 0x1e0) (z := 0x60) (c := 21) hR hW hsz rfl rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_calldatasize (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_calldatacopy (o := 0x240) (z := 0x60) (c := 21) hR hW hsz rfl rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_dup (n := 3) rfl (by hr) ?_
  refine rxm_mstore (o := 0x2a0) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_add (by hr) ?_
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
theorem rx_rl_s1A {sevm : Sevm} {b : Devm} {Gc : Nat} {r : Outcome} {M : Mem} {img : Bytes}
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
      SFunc.RunExact cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 r) :
    SFunc.RunExact cert.prog sevm (St b [3, 0x2a0] M (Gc + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 6 + 3 + 3 + 7 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1)) t_2cdb_c0 r := by
  have hctr := hL.ctr
  have hT := hL.supply
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  rw [hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ?_
  rw [keccak_one]
  refine rx_add (by hr) ?_
  refine rx_sload_sel hfork (by hr) ?_
  rw [getStorVal_eq, hB]
  refine rx_push rfl (by hr) ?_
  refine rx_calldataload (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_mul rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_dup (n := 4) rfl (by hr) ?_
  refine rx_dup (n := 3) rfl (by hr) ?_
  refine rx_div rfl (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_or rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hmulw ?_
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hT.read]
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hT0 ?_
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_div rfl (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x2c0) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x2e0) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x300) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x320) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x340) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x360) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_mul rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_calldataload (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  refine rx_lt rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hminw ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ?_
  rw [keccak_one]
  refine rx_add (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_sload_sel hfork (by hr) ?_
  rw [getStorVal_afterSload, getStorVal_eq, hB]
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hlew ?_
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_sub (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine k _ _ hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_
  · wchainT; exact hctr
  · wchainT; exact hT
  · intro j hj; wchainT; exact hL.amt j hj
  · wchainT

/-- `remove_liquidity`'s loop body up to `0x2e0c`, forward (variant B: loop head t_2cdb_c46,
memory size 0x5e0). -/
theorem rx_rl_s1B {sevm : Sevm} {b : Devm} {Gc : Nat} {r : Outcome} {M : Mem} {img : Bytes}
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
      SFunc.RunExact cert.prog sevm (St (afterSstore sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i))
        (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T))
        [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], B * rlAmt sevm / T, 3, 0x2a0] M' Gc) t_2e0c_c0 r) :
    SFunc.RunExact cert.prog sevm (St b [3, 0x2a0] M (Gc + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) (B - B * rlAmt sevm / T) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSload sevm b (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i) + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 5 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 2 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + sloadCost sevm b (balancesBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1)) t_2cdb_c46 r := by
  have hctr := hL.ctr
  have hT := hL.supply
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  rw [hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ?_
  rw [keccak_one]
  refine rx_add (by hr) ?_
  refine rx_sload_sel hfork (by hr) ?_
  rw [getStorVal_eq, hB]
  refine rx_push rfl (by hr) ?_
  refine rx_calldataload (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_mul rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_dup (n := 4) rfl (by hr) ?_
  refine rx_dup (n := 3) rfl (by hr) ?_
  refine rx_div rfl (by hr) ?_
  refine rx_eq rfl (by hr) ?_
  refine rx_or rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hmulw ?_
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hT.read]
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hT0 ?_
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_div rfl (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x2c0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x2e0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x300) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x320) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x340) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x360) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_mul rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_calldataload (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  refine rx_lt rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hminw ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl (by decide) (by hr) (by decide) ?_
  rw [keccak_one]
  refine rx_add (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_sload_sel hfork (by hr) ?_
  rw [getStorVal_afterSload, getStorVal_eq, hB]
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_iszero rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ hlew ?_
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_sub (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_sstore hfork (by have : gCallStipend = 2300 := rfl; omega) hstatic ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ?_
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_lt rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ?_
  refine k _ _ hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_
  · wchainT; exact hctr
  · wchainT; exact hT
  · intro j hj; wchainT; exact hL.amt j hj
  · wchainT

/-- The `transfer` payload with its two identity copies, forward (variant A: memory 0x380). -/
theorem rx_rl_s2A {sevm : Sevm} {b : Devm} {Gc : Nat} {r : Outcome} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x380) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 532 < 2 ^ 256)
    (k : ∀ b' M' img', BaseRel b b' → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x580 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunExact cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 r) :
    SFunc.RunExact cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 532)) t_2e0c_c0 r := by
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_mul rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rxm_mstore (o := 0x1e0 + 32 * i) (c := 3) hR hW hsz (off_amt hi)
    ⟨by rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩ ?_
  intro M hR hW hsz
  rw [memExtSize_of_le (by decide) (by omega)] at hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x400) (c := 19) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x420) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 4) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 5) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_gas (by hr) ?_
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
  refine rxm_identity (i := 0x420) (n := 4) (o := 0x480) (z := 4) (ext := 9) (X := 127) hid hdepth hR hW
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 4 = 18 by decide]; omega) (by omega) (by hr) ?_
  intro b2 M hsha hR hW hsz
  have hsel4 : (img1.sliceD 0x420 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_400.read]
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_caller (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_add (by hr) ?_
  refine rxm_mstore (o := 0x484) (c := 6) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_add (by hr) ?_
  refine rxm_mstore (o := 0x4a4) (c := 6) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.readWord_writeAt_self]
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_dup (n := 4) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_gas (by hr) ?_
  refine rxm_identity (i := 0x460) (n := 0x64) (o := 0x500) (z := 0x64) (ext := 16) (X := 143)
    (hid.of_rel hb12) hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 0x64 = 27 by decide]; omega) (by omega) (by hr) ?_
  intro b3 M hsha2 hR hW hsz
  rw [transfer_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2

  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  refine k b3 M img3 (hb12.trans hb23) hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_ _ _
  · rw [hI]; wchainT; exact f_ctr
  · rw [hI]; wchainT; exact f_T
  · intro j hj; rw [hI]; wchainT; exact f_amt j hj
  · rw [hI]; exact Region.write_self _ _ _

/-- The `transfer` payload with its two identity copies, forward (variant B: memory 0x5e0). -/
theorem rx_rl_s2B {sevm : Sevm} {b : Devm} {Gc : Nat} {r : Outcome} {M : Mem} {img : Bytes}
    {i : Nat} {T V : B256} {a : Nat → B256} (hi : i < 3)
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 V) (hG : 2000 ≤ Gc) (hGb : Gc + 482 < 2 ^ 256)
    (k : ∀ b' M' img', BaseRel b b' → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' i T (Function.update a i V) →
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)) →
      ∀ x y, SFunc.RunExact cert.prog sevm (St b' (x :: y :: [3, 0x2a0]) M' Gc) t_2ea7_c0 r) :
    SFunc.RunExact cert.prog sevm (St b [Nat.toB256 i, Bytes.toB256 [0x01, 0xe0], V, 3, 0x2a0] M
      (Gc + 482)) t_2e0c_c0 r := by
  refine rx_dest ?_
  refine rx_push rfl (by hr) ?_
  refine rx_mul rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rxm_mstore (o := 0x1e0 + 32 * i) (c := 3) hR hW hsz (off_amt hi)
    ⟨by rw [memExtSize_of_le (by decide) (by omega), Nat.sub_self]; rfl, by decide⟩ ?_
  intro M hR hW hsz
  rw [memExtSize_of_le (by decide) (by omega)] at hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x400) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x420) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 4) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 5) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_gas (by hr) ?_
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
  refine rxm_identity (i := 0x420) (n := 4) (o := 0x480) (z := 4) (ext := 0) (X := 118) hid hdepth hR hW
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 4 = 18 by decide]; omega) (by omega) (by hr) ?_
  intro b2 M hsha hR hW hsz
  have hsel4 : (img1.sliceD 0x420 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rxm_mload (o := 0x400) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_400.read]
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_caller (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_add (by hr) ?_
  refine rxm_mstore (o := 0x484) (c := 3) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read]
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_add (by hr) ?_
  refine rxm_mstore (o := 0x4a4) (c := 3) hR hW hsz (by decide) (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 1) rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rxm_mstore (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; intro M hR hW hsz
  refine rx_push rfl (by hr) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hr) ?_
  rw [Bytes.readWord_writeAt_self]
  refine rx_push rfl (by hr) ?_
  refine rx_add (by hr) ?_
  refine rx_dup (n := 0) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_dup (n := 2) rfl (by hr) ?_
  refine rx_dup (n := 4) rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_push rfl (by hr) ?_
  refine rx_gas (by hr) ?_
  refine rxm_identity (i := 0x460) (n := 0x64) (o := 0x500) (z := 0x64) (ext := 0) (X := 127)
    (hid.of_rel hb12) hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [show idCost 0x64 = 27 by decide]; omega) (by omega) (by hr) ?_
  intro b3 M hsha2 hR hW hsz
  rw [transfer_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2

  refine rx_push rfl (by hr) ?_
  refine rx_branch_succ (by decide) ?_
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  refine k b3 M img3 (hb12.trans hb23) hR hW (by rw [hsz]; decide) ⟨?_, ?_, ?_⟩ ?_ _ _
  · rw [hI]; wchainT; exact f_ctr
  · rw [hI]; wchainT; exact f_T
  · intro j hj; rw [hI]; wchainT; exact f_amt j hj
  · rw [hI]; exact Region.write_self _ _ _

end Blanc.Lift.Curve3Pool
