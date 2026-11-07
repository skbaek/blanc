import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.KeepSel
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
    {img : Bytes} (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hSK : KeepTok sevm ((b.getStor sevm.currentTarget).get tokenSlot) L)
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
      b1.logs = b.logs ∧ b1.output = b.output ∧ Devm.AccGrow b b1 ∧ b1.getCode 4 = b.getCode 4 ∧
      (∀ a, b.getCode a ≠ .empty → b1.getCode a = b.getCode a) ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      WordAt img1 0x140 (Bytes.toB256 (c.post.output.take 32)) ∧
      (∀ j < 6, WordAt img1 (0x1e0 + 32 * j) 0) ∧ WordAt img1 0x2a0 0 ∧
      XAt sevm post 0x2cdb (St b1 [3, 0x2a0] M1 G1) L' := by
  xs 0x2c6c (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x2c6d (.reg .sload) ri_sloadF
  xa 2
  xji 0x2c72 0x2c76 hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xa 3
  xw 0x2c7e (.reg .sstore) ri_sstoreF
  xa 3
  xji 0x2c84 0x2c88 hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  refine ⟨hlock, hval, ?_⟩
  xa 6
  xmo 0x2c99 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  xa 2
  xw 0x2c9f (.reg .sload) ri_sloadF
  xs 0x2ca0 (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_imgH (pc' := 0x2ca1) (i := 0x17c) (n := 4) (o := 0x1c0) (z := 0x20) hfork.stateGas_none (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M, L1, h, ⟨d0, hrun0, hcd0⟩, hR, hW, hrd, hob, hstor, hlogs, hk⟩ := h
  xs 0x2ca4 (.push [0x2c, 0xa9] (by decide)) ri_push
  xji 0x2ca5 0x2ca9 hw
  · xdead
  have htok' : ((afterSstoreH sevm (afterSloadH sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])).getStorVal sevm.currentTarget
      (Bytes.toB256 [5])) = (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [lockSlot_lit, tokenSlot_lit, getStorVal_afterSstoreH_ne lock_ne_token, getStorVal_afterSloadH]
    rfl
  rw [htok'] at hk hrun0
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout, hclogs, hcpre,
    hcpost⟩
  · exact absurd hpre htok
  have h4 : d1.getCode 4 = b.getCode 4 := by
    rw [hcpost, (hSK c (by rw [hL]; exact List.mem_cons_self) htgt).2, hcpre, afterSloadH_getCode,
      afterSstoreH_getCode, afterSloadH_getCode]
  clear hk
  xa 5
  xji 0x2cb2 0x2cb6 hw2
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := B256.lt_of_gtCheck_ne_zero hw2
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw2
  xa 4
  xmo 0x2cbe (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  xs 0x2cc1 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x2cc2 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  xa 3
  xmo 0x2cc9 (.reg .calldatacopy) (ri_calldatacopy_imgAt (o := 0x1e0) (z := 0x60) rfl rfl)
  xa 3
  xmo 0x2cd0 (.reg .calldatacopy) (ri_calldatacopy_imgAt (o := 0x240) (z := 0x60) rfl rfl)
  xa 5
  xmo 0x2cda (.reg .mstore) (ri_mstore_imgAt (o := 0x2a0) rfl)
  xs 0x2cdb (.reg .add) ri_add
  clear * - h h4 hR hW hL hdepth htgt hdata hstat hcout hlen hclogs hcpre hcpost hstor hlogs hout hacc hcodeK hob
    hrd hcd
  rw [show [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [2, 160]] = ([3, 0x2a0] : List B256)
    by decide] at h
  refine ⟨c, L1, d1, M, _, _, hL, hdepth, htgt, ?_, hstat, by rw [hcout]; exact hlen, hclogs, ?_, hcpost,
    ?_, ?_, ?_, ?_, ?_, h4, ?_, hR, hW, ?_, ?_, ?_, h⟩
  · rw [hdata, Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide)
      (by rw [B256.length_toBytes])]
    decide
  · intro a
    rw [hcpre, afterSloadH_getCode, afterSstoreH_getCode, afterSloadH_getCode]
  · intro x
    rw [hstor, afterSloadH_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, lockSlot_lit]
    rfl
  · intro a ha
    rw [hstor, afterSloadH_getStor, afterSstoreH_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSloadH_getStor]
  · rw [hlogs, afterSloadH_logs, afterSstoreH_logs, afterSloadH_logs]
  · rw [hout, afterSloadH_output, afterSstoreH_output, afterSloadH_output]
  · refine Devm.AccGrow.trans (Devm.AccGrow.of_eq ?_) hacc
    rw [afterSloadH_accessedAddresses, afterSstoreH_accessedAddresses, afterSloadH_accessedAddresses]
  · intro a ha
    have e := hcodeK a (by rwa [afterSloadH_getCode, afterSstoreH_getCode, afterSloadH_getCode])
    rwa [afterSloadH_getCode, afterSstoreH_getCode, afterSloadH_getCode] at e
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
