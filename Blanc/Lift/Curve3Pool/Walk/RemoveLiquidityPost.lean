import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLoop

/-!
# `remove_liquidity`, part 3: after the loop

From the loop's exit (`0x2f7b`) to `STOP`: `CurveToken(lp_token).burnFrom(msg.sender, _amount)`
(a `CALL` whose output must be at least a word), the `RemoveLiquidity` event (`LOG2` over the
three amounts, the three zero fees and `total_supply - _amount`, checked), and the reentrancy
lock cleared.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

theorem burn_sel_bytes :
    (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes = List.replicate 28 0 ++ burnFromSel := by
  decide

/-- The `burnFrom` calldata the three writes leave at `0x61c`. -/
theorem burn_input (img : Bytes) (C A : B256) :
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x600
      (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes) 0x620 C.toBytes) 0x640 A.toBytes).sliceD
      0x61c 0x44 0 = burnFromSel ++ C.toBytes ++ A.toBytes := by
  have hsel : Region (Bytes.writeAt img 0x600 (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes)
      0x61c burnFromSel := by
    have := Region.write_self img 0x600 (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes
    rw [burn_sel_bytes] at this
    exact this.right
  refine Region.slice (Region.append' (o' := 0x640) (Region.append' (o' := 0x620) ?_ ?_ (by rfl))
    ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  · refine Region.write_other (Region.write_other hsel ?_) ?_ <;>
      simp only [burnFromSel, B256.length_toBytes, List.length_cons, List.length_nil] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
  · exact Region.write_self _ _ _

/-- **After the loop** (`0x2f7b` → `STOP`). The last remaining child is
`token.burnFrom(msg.sender, _amount)` (value `0`, at least a word returned); the frame then
logs `RemoveLiquidity(msg.sender, amounts, fees, total_supply - _amount)` from the six words at
`0x1e0` and clears the lock. -/
theorem xa_rl_post {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {T tw : B256} {a : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hT : WordAt img 0x140 T)
    (hamt : ∀ j, j < 6 → WordAt img (0x1e0 + 32 * j) (a j))
    (htw : (b.getStor sevm.currentTarget).get tokenSlot = tw)
    (htok : ¬ sevm.benvStat.rules.isPrecomp tw.toAdr)
    (h : XAt sevm post 0x2f7b (St b [3, 0x2a0] M G) L) :
    ¬ T < rlAmt sevm ∧ ∃ c d, L = [c] ∧
      ChildOf b d tw.toAdr (burnFromSel ++ sevm.caller.toB256.toBytes ++ (rlAmt sevm).toBytes) 0
        sevm.isStatic c ∧ 32 ≤ c.post.output.length ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        ((d.getStor sevm.currentTarget).set lockSlot 0).get x) ∧
      post.logs = d.logs ++ [⟨sevm.currentTarget,
        [Bytes.toB256 [0xa4, 0x9d, 0x4c, 0xf0, 0x26, 0x56, 0xae, 0xbf, 0x8c, 0x77, 0x1f, 0x5a, 0x85,
          0x85, 0x63, 0x8a, 0x2a, 0x15, 0xee, 0x6c, 0x97, 0xcf, 0x72, 0x05, 0xd4, 0x20, 0x8e, 0xd7,
          0xc1, 0xdf, 0x25, 0x2d], sevm.caller.toB256],
        (a 0).toBytes ++ (a 1).toBytes ++ (a 2).toBytes ++ (a 3).toBytes ++ (a 4).toBytes ++
          (a 5).toBytes ++ (T - rlAmt sevm).toBytes⟩] ∧
      post.output = d.output := by
  xjd 0x2f7c
  xs 0x2f7d (.reg .pop) ri_pop
  xs 0x2f7e (.reg .pop) ri_pop
  xs 0x2f80 (.push [0x20] (by decide)) ri_push
  xs 0x2f83 (.push [0x06, 0xa0] (by decide)) ri_push
  xs 0x2f85 (.push [0x44] (by decide)) ri_push
  xs 0x2f8a (.push [0x79, 0xcc, 0x67, 0x90] (by decide)) ri_push
  xs 0x2f8d (.push [0x06, 0x00] (by decide)) ri_push
  xmo 0x2f8e (.reg .mstore) (ri_mstore_imgAt (o := 0x600) rfl)
  xs 0x2f8f (.reg .caller) ri_caller
  xs 0x2f92 (.push [0x06, 0x20] (by decide)) ri_push
  xmo 0x2f93 (.reg .mstore) (ri_mstore_imgAt (o := 0x620) rfl)
  xs 0x2f95 (.push [0x04] (by decide)) ri_push
  xs 0x2f96 (.reg .calldataload) ri_calldataload
  xs 0x2f99 (.push [0x06, 0x40] (by decide)) ri_push
  xmo 0x2f9a (.reg .mstore) (ri_mstore_imgAt (o := 0x640) rfl)
  xs 0x2f9d (.push [0x06, 0x1c] (by decide)) ri_push
  xs 0x2f9f (.push [0x00] (by decide)) ri_push
  xs 0x2fa1 (.push [0x05] (by decide)) ri_push
  xw 0x2fa2 (.reg .sload) ri_sload
  rw [tokenSlot_lit, getStorVal_eq, htw] at h
  xs 0x2fa3 (.reg .gas) ri_gas_remaining
  replace h := xa_call_img (pc' := 0x2fa4) (i := 0x61c) (n := 0x44) (o := 0x6a0) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, flag, L1, h, hrd, hk⟩ := h
  rw [burn_input] at hk
  xs 0x2fa7 (.push [0x2f, 0xac] (by decide)) ri_push
  xji 0x2fa8 0x2fac hw
  · xdead
  obtain ⟨hR, hW, hout, hch⟩ := hk hw
  clear hk hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp htok
  have hc' : ChildOf b d tw.toAdr (burnFromSel ++ sevm.caller.toB256.toBytes ++
      (rlAmt sevm).toBytes) 0 sevm.isStatic c := by
    rw [zero_lit] at hc
    exact hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
      (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _)
  clear hc
  xjd 0x2fad
  xs 0x2faf (.push [0x1f] (by decide)) ri_push
  xs 0x2fb0 (.reg .returndatasize) ri_returndatasize
  xs 0x2fb1 (.reg .gt) ri_gt
  xs 0x2fb4 (.push [0x2f, 0xb9] (by decide)) ri_push
  xji 0x2fb5 0x2fb9 hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have := gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at this
    rw [hc'.output]; omega
  clear hw
  have e1 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img1, hR, hI⟩ := e1
  have f_T : WordAt img1 0x140 T := by rw [hI]; wchain; exact hT
  have f_amt : ∀ j, j < 6 → WordAt img1 (0x1e0 + 32 * j) (a j) := by
    intro j hj; rw [hI]; wchain; exact hamt j hj
  clear hI hT hamt
  xjd 0x2fba
  xs 0x2fbc (.push [0x00] (by decide)) ri_push
  xs 0x2fbd (.reg .pop) ri_pop
  xs 0x2fc0 (.push [0x06, 0xa0] (by decide)) ri_push
  xs 0x2fc1 (.reg .pop) ri_pop
  xs 0x2fc4 (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x2fc5 (.reg .mload) (ri_mload_imgAt (o := 0x1e0) rfl)
  rw [(f_amt 0 (by decide)).read] at h
  xs 0x2fc8 (.push [0x06, 0xc0] (by decide)) ri_push
  xmo 0x2fc9 (.reg .mstore) (ri_mstore_imgAt (o := 0x6c0) rfl)
  xs 0x2fcc (.push [0x02, 0x00] (by decide)) ri_push
  xmo 0x2fcd (.reg .mload) (ri_mload_imgAt (o := 0x200) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), (f_amt 1 (by decide)).read] at h
  xs 0x2fd0 (.push [0x06, 0xe0] (by decide)) ri_push
  xmo 0x2fd1 (.reg .mstore) (ri_mstore_imgAt (o := 0x6e0) rfl)
  xs 0x2fd4 (.push [0x02, 0x20] (by decide)) ri_push
  xmo 0x2fd5 (.reg .mload) (ri_mload_imgAt (o := 0x220) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [(f_amt 2 (by decide)).read] at h
  xs 0x2fd8 (.push [0x07, 0x00] (by decide)) ri_push
  xmo 0x2fd9 (.reg .mstore) (ri_mstore_imgAt (o := 0x700) rfl)
  xs 0x2fdc (.push [0x02, 0x40] (by decide)) ri_push
  xmo 0x2fdd (.reg .mload) (ri_mload_imgAt (o := 0x240) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [(f_amt 3 (by decide)).read] at h
  xs 0x2fe0 (.push [0x07, 0x20] (by decide)) ri_push
  xmo 0x2fe1 (.reg .mstore) (ri_mstore_imgAt (o := 0x720) rfl)
  xs 0x2fe4 (.push [0x02, 0x60] (by decide)) ri_push
  xmo 0x2fe5 (.reg .mload) (ri_mload_imgAt (o := 0x260) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [(f_amt 4 (by decide)).read] at h
  xs 0x2fe8 (.push [0x07, 0x40] (by decide)) ri_push
  xmo 0x2fe9 (.reg .mstore) (ri_mstore_imgAt (o := 0x740) rfl)
  xs 0x2fec (.push [0x02, 0x80] (by decide)) ri_push
  xmo 0x2fed (.reg .mload) (ri_mload_imgAt (o := 0x280) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [(f_amt 5 (by decide)).read] at h
  xs 0x2ff0 (.push [0x07, 0x60] (by decide)) ri_push
  xmo 0x2ff1 (.reg .mstore) (ri_mstore_imgAt (o := 0x760) rfl)
  xs 0x2ff4 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x2ff5 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [f_T.read] at h
  xs 0x2ff7 (.push [0x04] (by decide)) ri_push
  xs 0x2ff8 (.reg .calldataload) ri_calldataload
  xs 0x2ff9 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2ffa (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2ffb (.reg .lt) ri_lt
  xs 0x2ffc (.reg .iszero) ri_iszero
  xs 0x2fff (.push [0x30, 0x04] (by decide)) ri_push
  xji 0x3000 0x3004 hw
  · xdead
  have hTa := ltCheck_eq_zero (eqCheck_ne_zero hw)
  clear hw
  xjd 0x3005
  xs 0x3006 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x3007 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x3008 (.reg .sub) ri_sub
  xs 0x3009 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x300a (.reg .pop) ri_pop
  xs 0x300b (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x300c (.reg .pop) ri_pop
  xs 0x300f (.push [0x07, 0x80] (by decide)) ri_push
  xmo 0x3010 (.reg .mstore) (ri_mstore_imgAt (o := 0x780) rfl)
  xs 0x3011 (.reg .caller) ri_caller
  xs 0x3032 (.push [0xa4, 0x9d, 0x4c, 0xf0, 0x26, 0x56, 0xae, 0xbf, 0x8c, 0x77, 0x1f, 0x5a, 0x85, 0x85, 0x63, 0x8a, 0x2a, 0x15, 0xee, 0x6c, 0x97, 0xcf, 0x72, 0x05, 0xd4, 0x20, 0x8e, 0xd7, 0xc1, 0xdf, 0x25, 0x2d] (by decide)) ri_push
  xs 0x3034 (.push [0xe0] (by decide)) ri_push
  xs 0x3037 (.push [0x06, 0xc0] (by decide)) ri_push
  have e2 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img2, hR, hI⟩ := e2
  have hdata : Region img2 0x6c0 ((a 0).toBytes ++ (a 1).toBytes ++ (a 2).toBytes ++
      (a 3).toBytes ++ (a 4).toBytes ++ (a 5).toBytes ++ (T - rlAmt sevm).toBytes) := by
    rw [hI]
    refine Region.append' (o' := 0x780) (Region.append' (o' := 0x760)
      (Region.append' (o' := 0x740) (Region.append' (o' := 0x720) (Region.append' (o' := 0x700)
      (Region.append' (o' := 0x6e0) ?_ ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
    all_goals first
      | simp only [List.length_append, B256.length_toBytes]
      | exact Region.of_word (by wchain)
  clear hI
  replace h := xa_nextAt (n := .reg (.log 2)) (pc' := 0x3038) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log2_post s
  clear s
  rw [Mem.Reads.read hR, show (Bytes.toB256 [0x06, 0xc0]).toNat = 0x6c0 from rfl,
    show (Bytes.toB256 [0xe0]).toNat = 0xe0 from rfl,
    hdata.slice (by simp only [List.length_append, B256.length_toBytes])] at h
  xs 0x303a (.push [0x00] (by decide)) ri_push
  xs 0x303e (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x303f (.reg .sstore) ri_sstore
  obtain ⟨hrun, hL⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  have hp := (Except.ok.inj hrun).symm
  subst hp hL
  refine ⟨hTa, c, d, rfl, hc', hlen, ?_, ?_, ?_⟩
  · intro x
    show ((afterSstore sevm _ _ _).getStor _).get x = _
    rw [afterSstore_getStor_self, lockSlot_lit, zero_lit]
    rfl
  · show (afterSstore sevm _ _ _).logs = _
    rw [afterSstore_logs]
    rfl
  · show (afterSstore sevm _ _ _).output = _
    rw [afterSstore_output]
    rfl

end Blanc.Lift.Curve3Pool
