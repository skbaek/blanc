import Blanc.Lift.Curve3Pool.Walk.Kit

/-!
# `remove_liquidity`, part 1: the lock, the value guard and the supply

From the arm's body (`0x2c68`, after the dispatcher's test) to the loop head (`0x2cdb`):
`assert lock == 0; lock = 1`, the non-payable guard, `total_supply = token.totalSupply()`
(a `STATICCALL` whose reply must be at least 32 bytes), `amounts` and `fees` zeroed by two
`CALLDATACOPY`s past the calldata, and the loop counter at `0x2a0` set to `0`.

`xa_rl_pre`: the lock was clear and the call carried no value; the frame's next child is the
`totalSupply()` call to the stored token (static, at least 32 bytes back, no logs); the base
after it holds the pool's storage with the lock set and every other account's storage unchanged;
the memory image has the supply word at `0x140`, zero `amounts`/`fees`, and counter `0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`remove_liquidity` up to its loop** (see the module note). -/
theorem xa_rl_pre {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x2c68 (St b [] M G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (b1 : Devm) (M1 : Mem) (G1 : Nat) (img1 : Bytes),
      L = c :: L' ∧ 0 < sevm.depth ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get tokenSlot).toAdr ∧
      c.sevm.data = totalSupplyData ∧ c.sevm.isStatic = true ∧ 32 ≤ c.post.output.length ∧
      c.post.logs = [] ∧ (∀ a, c.pre.getCode a = b.getCode a) ∧
      (∀ a, b1.getCode a = c.post.getCode a) ∧
      (∀ x, (b1.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) ∧
      (∀ a, a ≠ sevm.currentTarget → b1.getStor a = b.getStor a) ∧
      b1.logs = b.logs ∧ b1.output = b.output ∧ Devm.AccGrow b b1 ∧
      (∀ a, b.getCode a ≠ .empty → b1.getCode a = b.getCode a) ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      WordAt img1 0x140 (Bytes.toB256 (c.post.output.take 32)) ∧
      (∀ j < 6, WordAt img1 (0x1e0 + 32 * j) 0) ∧ WordAt img1 0x2a0 0 ∧
      XAt sevm post 0x2cdb (St b1 [3, 0x2a0] M1 G1) L' := by
  xs 0x2c6c (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x2c6d (.reg .sload) ri_sload
  xs 0x2c6e (.reg .iszero) ri_iszero
  xs 0x2c71 (.push [0x2c, 0x76] (by decide)) ri_push
  xji 0x2c72 0x2c76 hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xjd 0x2c77
  xs 0x2c79 (.push [0x01] (by decide)) ri_push
  xs 0x2c7d (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x2c7e (.reg .sstore) ri_sstore
  xs 0x2c7f (.reg .callvalue) ri_callvalue
  xs 0x2c80 (.reg .iszero) ri_iszero
  xs 0x2c83 (.push [0x2c, 0x88] (by decide)) ri_push
  xji 0x2c84 0x2c88 hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  refine ⟨hlock, hval, ?_⟩
  xjd 0x2c89
  xs 0x2c8b (.push [0x20] (by decide)) ri_push
  xs 0x2c8e (.push [0x01, 0xc0] (by decide)) ri_push
  xs 0x2c90 (.push [0x04] (by decide)) ri_push
  xs 0x2c95 (.push [0x18, 0x16, 0x0d, 0xdd] (by decide)) ri_push
  xs 0x2c98 (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x2c99 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  xs 0x2c9c (.push [0x01, 0x7c] (by decide)) ri_push
  xs 0x2c9e (.push [0x05] (by decide)) ri_push
  xw 0x2c9f (.reg .sload) ri_sload
  xs 0x2ca0 (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x2ca1) (i := 0x17c) (n := 4) (o := 0x1c0) (z := 0x20)
    hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M, L1, h, hR, hW, hrd, hob, hstor, hlogs, hk⟩ := h
  xs 0x2ca4 (.push [0x2c, 0xa9] (by decide)) ri_push
  xji 0x2ca5 0x2ca9 hw
  · xdead
  have htok' : ((afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])).getStorVal sevm.currentTarget
      (Bytes.toB256 [5])) = (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [lockSlot_lit, tokenSlot_lit, getStorVal_afterSstore_ne lock_ne_token, getStorVal_afterSload]
    rfl
  rw [htok'] at hk
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout, hclogs, hcpre,
    hcpost⟩
  · exact absurd hpre htok
  clear hk
  xjd 0x2caa
  xs 0x2cac (.push [0x1f] (by decide)) ri_push
  xs 0x2cad (.reg .returndatasize) ri_returndatasize
  xs 0x2cae (.reg .gt) ri_gt
  xs 0x2cb1 (.push [0x2c, 0xb6] (by decide)) ri_push
  xji 0x2cb2 0x2cb6 hw2
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := gtCheck_ne_zero hw2
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw2
  xjd 0x2cb7
  xs 0x2cb9 (.push [0x00] (by decide)) ri_push
  xs 0x2cba (.reg .pop) ri_pop
  xs 0x2cbd (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0x2cbe (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  xs 0x2cc1 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x2cc2 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  xs 0x2cc4 (.push [0x60] (by decide)) ri_push
  xs 0x2cc5 (.reg .calldatasize) ri_calldatasize
  xs 0x2cc8 (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x2cc9 (.reg .calldatacopy) (ri_calldatacopy_imgAt (o := 0x1e0) (z := 0x60) rfl rfl)
  xs 0x2ccb (.push [0x60] (by decide)) ri_push
  xs 0x2ccc (.reg .calldatasize) ri_calldatasize
  xs 0x2ccf (.push [0x02, 0x40] (by decide)) ri_push
  xmo 0x2cd0 (.reg .calldatacopy) (ri_calldatacopy_imgAt (o := 0x240) (z := 0x60) rfl rfl)
  xs 0x2cd3 (.push [0x02, 0xa0] (by decide)) ri_push
  xs 0x2cd5 (.push [0x00] (by decide)) ri_push
  xs 0x2cd7 (.push [0x03] (by decide)) ri_push
  xs 0x2cd8 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2cd9 (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x2cda (.reg .mstore) (ri_mstore_imgAt (o := 0x2a0) rfl)
  xs 0x2cdb (.reg .add) ri_add
  clear * - h hR hW hL hdepth htgt hdata hstat hcout hlen hclogs hcpre hcpost hstor hlogs hout hacc hcodeK hob
    hrd hcd
  rw [show [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [2, 160]] = ([3, 0x2a0] : List B256)
    by decide] at h
  refine ⟨c, L1, d1, M, _, _, hL, hdepth, htgt, ?_, hstat, by rw [hcout]; exact hlen, hclogs, ?_, hcpost,
    ?_, ?_, ?_, ?_, ?_, ?_, hR, hW, ?_, ?_, ?_, h⟩
  · rw [hdata, Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide)
      (by rw [B256.length_toBytes])]
    decide
  · intro a
    rw [hcpre, afterSload_getCode, afterSstore_getCode, afterSload_getCode]
  · intro x
    rw [hstor, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor, lockSlot_lit]
    rfl
  · intro a ha
    rw [hstor, afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]
  · rw [hlogs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [hout, afterSload_output, afterSstore_output, afterSload_output]
  · refine Devm.AccGrow.trans (Devm.AccGrow.of_eq ?_) hacc
    rw [afterSload_accessedAddresses, afterSstore_accessedAddresses, afterSload_accessedAddresses]
  · intro a ha
    have e := hcodeK a (by rwa [afterSload_getCode, afterSstore_getCode, afterSload_getCode])
    rwa [afterSload_getCode, afterSstore_getCode, afterSload_getCode] at e
  · have hZ : List.sliceD sevm.data (Nat.toB256 (List.length sevm.data)).toNat 96 0 =
        List.replicate 96 0 := by
      rw [B256.toNat_toB256_of_lt hcd]; exact List.sliceD_length_eq
    rw [hZ]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other ?_ (.inl (by decide)))
      (.inl (by decide))) (.inl (by decide))
    have hTw : List.sliceD (Bytes.writeAt (Bytes.writeAt img 352 (Bytes.toB256 [24, 22, 13, 221]).toBytes)
        448 (List.take 32 out)) 448 32 0 = List.take 32 out := by
      rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (le_refl _)
        (by rw [List.length_take]; omega), Nat.sub_self]
      exact List.sliceD_zero_of_length (by rw [List.length_take]; omega)
    rw [hTw, hcout]
    exact WordAt.write_self _ _ _
  · have hZ : List.sliceD sevm.data (Nat.toB256 (List.length sevm.data)).toNat 96 0 =
        List.replicate 96 0 := by
      rw [B256.toNat_toB256_of_lt hcd]; exact List.sliceD_length_eq
    rw [hZ]
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
  · rw [zero_lit]
    exact WordAt.write_self _ _ _

end Blanc.Lift.Curve3Pool
