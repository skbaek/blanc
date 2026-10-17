import Blanc.Lift.Curve3Pool.Walk.AddLiquidityFrames
import Blanc.Lift.Curve3Pool.Walk.Dispatch

/-!
# `add_liquidity`, part 1: the guards, the fee and `_A`

From the dispatcher to `0xf05`: `assert lock == 0; lock = 1`, the non-payable guard,
`assert not is_killed`, `fees` zeroed past the calldata, `_fee = fee * 3 / 8` (checked) and
`_admin_fee`, then `amp = self._A()` with the six-word inline frame save and restore.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

theorem feeSlot_lit : Bytes.toB256 [0x02] = feeSlot := by decide
theorem adminFeeSlot_lit : Bytes.toB256 [0x03] = adminFeeSlot := by decide
theorem isKilledSlot_lit : Bytes.toB256 [0x0f] = isKilledSlot := by decide

/-- **The dispatcher hands `add_liquidity` its body** (past the arm's own test), with the
prologue's exact memory and the frame's remaining children unchanged. -/
theorem xa_dispatch_addLiquidity {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0xe55 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x2 (.push [0x04] (by decide)) ri_push  -- 0000 PUSH1 0x04
  xs 0x3 (.reg .calldatasize) ri_calldatasize  -- 0002 CALLDATASIZE
  xs 0x4 (.reg .lt) ri_lt  -- 0003 LT
  xs 0x5 (.reg .iszero) ri_iszero  -- 0004 ISZERO
  xs 0x8 (.push [0x00, 0x0d] (by decide)) ri_push  -- 0005 PUSH2 0x000d
  xji 0x9 0xd hw  -- taken
  · exact absurd (eqCheck_eq_zero hw) (by
      rw [ltCheck_eq_zero_of_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide)
  xjd 0xe
  xs 0x10 (.push [0x00] (by decide)) ri_push  -- 000e PUSH1 0x00
  xs 0x11 (.reg .calldataload) ri_calldataload  -- 0010 CALLDATALOAD
  xs 0x13 (.push [0x1c] (by decide)) ri_push  -- 0011 PUSH1 0x1c
  xs 0x14 (.reg .mstore) ri_mstore  -- 0013 MSTORE
  xs 0x2a (.push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0014 PUSH21 0x010000000000000000000000000000000000000000
  xs 0x2c (.push [0x20] (by decide)) ri_push  -- 002a PUSH1 0x20
  xs 0x2d (.reg .mstore) ri_mstore  -- 002c MSTORE
  xs 0x3e (.push [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) ri_push  -- 002d PUSH16 0x7fffffffffffffffffffffffffffffff
  xs 0x40 (.push [0x40] (by decide)) ri_push  -- 003e PUSH1 0x40
  xs 0x41 (.reg .mstore) ri_mstore  -- 0040 MSTORE
  xs 0x62 (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0041 PUSH32 0xffffffffffffffffffffffffffffffff80000000000000000000000000000000
  xs 0x64 (.push [0x60] (by decide)) ri_push  -- 0062 PUSH1 0x60
  xs 0x65 (.reg .mstore) ri_mstore  -- 0064 MSTORE
  xs 0x7b (.push [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00] (by decide)) ri_push  -- 0065 PUSH21 0x012a05f1fffffffffffffffffffffffffdabf41c00
  xs 0x7d (.push [0x80] (by decide)) ri_push  -- 007b PUSH1 0x80
  xs 0x7e (.reg .mstore) ri_mstore  -- 007d MSTORE
  xs 0x9f (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 007e PUSH32 0xfffffffffffffffffffffffed5fa0e0000000000000000000000000000000000
  xs 0xa1 (.push [0xa0] (by decide)) ri_push  -- 009f PUSH1 0xa0
  xs 0xa2 (.reg .mstore) ri_mstore  -- 00a1 MSTORE
  replace h : XAt sevm post 0xa2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) _) L := h
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0x4515cef3 := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; exact hsel
  xs 0xa4 (.push [0x00] (by decide)) ri_push  -- 00a2 PUSH1 0x00
  xs 0xa5 (.reg .iszero) ri_iszero  -- 00a4 ISZERO
  xs 0xa8 (.push [0x02, 0x44] (by decide)) ri_push  -- 00a5 PUSH2 0x0244
  xji 0xa9 0x244 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x245
  xs 0x24a (.push [0xf4, 0x46, 0xc1, 0xd0] (by decide)) ri_push  -- 0245 PUSH4 0xf446c1d0
  xs 0x24c (.push [0x00] (by decide)) ri_push  -- 024a PUSH1 0x00
  xs 0x24d (.reg .mload) ri_mload_vy0  -- 024c MLOAD
  xs 0x24e (.reg .eq) ri_eq  -- 024d EQ
  xs 0x24f (.reg .iszero) ri_iszero  -- 024e ISZERO
  xs 0x252 (.push [0x02, 0x79] (by decide)) ri_push  -- 024f PUSH2 0x0279
  xji 0x253 0x279 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x27a
  xs 0x27c (.push [0x00] (by decide)) ri_push  -- 027a PUSH1 0x00
  xs 0x27d (.reg .iszero) ri_iszero  -- 027c ISZERO
  xs 0x280 (.push [0x03, 0x99] (by decide)) ri_push  -- 027d PUSH2 0x0399
  xji 0x281 0x399 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x39a
  xs 0x39c (.push [0x00] (by decide)) ri_push  -- 039a PUSH1 0x00
  xs 0x39d (.reg .iszero) ri_iszero  -- 039c ISZERO
  xs 0x3a0 (.push [0x04, 0xc1] (by decide)) ri_push  -- 039d PUSH2 0x04c1
  xji 0x3a1 0x4c1 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x4c2
  xs 0x4c4 (.push [0x00] (by decide)) ri_push  -- 04c2 PUSH1 0x00
  xs 0x4c5 (.reg .iszero) ri_iszero  -- 04c4 ISZERO
  xs 0x4c8 (.push [0x07, 0xaf] (by decide)) ri_push  -- 04c5 PUSH2 0x07af
  xji 0x4c9 0x7af hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x7b0
  xs 0x7b2 (.push [0x00] (by decide)) ri_push  -- 07b0 PUSH1 0x00
  xs 0x7b3 (.reg .iszero) ri_iszero  -- 07b2 ISZERO
  xs 0x7b6 (.push [0x09, 0x0d] (by decide)) ri_push  -- 07b3 PUSH2 0x090d
  xji 0x7b7 0x90d hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x90e
  xs 0x913 (.push [0xbb, 0x7b, 0x8b, 0x80] (by decide)) ri_push  -- 090e PUSH4 0xbb7b8b80
  xs 0x915 (.push [0x00] (by decide)) ri_push  -- 0913 PUSH1 0x00
  xs 0x916 (.reg .mload) ri_mload_vy0  -- 0915 MLOAD
  xs 0x917 (.reg .eq) ri_eq  -- 0916 EQ
  xs 0x918 (.reg .iszero) ri_iszero  -- 0917 ISZERO
  xs 0x91b (.push [0x0a, 0xf8] (by decide)) ri_push  -- 0918 PUSH2 0x0af8
  xji 0x91c 0xaf8 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0xaf9
  xs 0xafe (.push [0x38, 0x83, 0xe1, 0x19] (by decide)) ri_push  -- 0af9 PUSH4 0x3883e119
  xs 0xb00 (.push [0x00] (by decide)) ri_push  -- 0afe PUSH1 0x00
  xs 0xb01 (.reg .mload) ri_mload_vy0  -- 0b00 MLOAD
  xs 0xb02 (.reg .eq) ri_eq  -- 0b01 EQ
  xs 0xb03 (.reg .iszero) ri_iszero  -- 0b02 ISZERO
  xs 0xb06 (.push [0x0e, 0x46] (by decide)) ri_push  -- 0b03 PUSH2 0x0e46
  xji 0xb07 0xe46 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0xe47
  xs 0xe4c (.push [0x45, 0x15, 0xce, 0xf3] (by decide)) ri_push  -- 0e47 PUSH4 0x4515cef3
  xs 0xe4e (.push [0x00] (by decide)) ri_push  -- 0e4c PUSH1 0x00
  xs 0xe4f (.reg .mload) ri_mload_vy0  -- 0e4e MLOAD
  xs 0xe50 (.reg .eq) ri_eq  -- 0e4f EQ
  xs 0xe51 (.reg .iszero) ri_iszero  -- 0e50 ISZERO
  xs 0xe54 (.push [0x18, 0x9c] (by decide)) ri_push  -- 0e51 PUSH2 0x189c
  xji 0xe55 0x189c hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [hsw]; decide) (isNe_jump hw)

/-- The base after `add_liquidity`'s guards and fee reads. -/
def alB1 (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm (afterSstore sevm (afterSload sevm b
    (Bytes.toB256 [0xff, 0xff, 0xff])) (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0x01]))
    (Bytes.toB256 [0x0f])) feeSlot) adminFeeSlot


/-- A word inside a zero fill reads `0`. -/
theorem al_zeroWord (img : Bytes) {o n j : Nat} (hj : 32 * j + 32 ≤ n) :
    WordAt (Bytes.writeAt img o (List.replicate n 0)) (o + 32 * j) 0 := by
  unfold WordAt
  rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]; omega),
    List.sliceD_replicate_zero]
  decide

/-- Setting the lock keeps the storage abstraction. -/
theorem al_abstracts_lock {σ : Stor} {s : State} (h : Abstracts σ s) (v : B256) :
    Abstracts (σ.set lockSlot v) s where
  coins i := by
    rw [Stor.get_set_ne _ ((by decide : ∀ i : Fin 3, lockSlot ≠ coinSlot i) i)]; exact h.coins i
  balances i := by
    rw [Stor.get_set_ne _ ((by decide : ∀ i : Fin 3, lockSlot ≠ balanceSlot i) i)]
    exact h.balances i
  fee := by rw [Stor.get_set_ne _ (by decide)]; exact h.fee
  adminFee := by rw [Stor.get_set_ne _ (by decide)]; exact h.adminFee
  owner := by rw [Stor.get_set_ne _ (by decide)]; exact h.owner
  token := by rw [Stor.get_set_ne _ (by decide)]; exact h.token
  initialA := by rw [Stor.get_set_ne _ (by decide)]; exact h.initialA
  futureA := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureA
  initialATime := by rw [Stor.get_set_ne _ (by decide)]; exact h.initialATime
  futureATime := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureATime
  adminActionsDeadline := by rw [Stor.get_set_ne _ (by decide)]; exact h.adminActionsDeadline
  transferOwnershipDeadline := by
    rw [Stor.get_set_ne _ (by decide)]; exact h.transferOwnershipDeadline
  futureFee := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureFee
  futureAdminFee := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureAdminFee
  futureOwner := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureOwner
  isKilled := by rw [Stor.get_set_ne _ (by decide)]; exact h.isKilled
  killDeadline := by rw [Stor.get_set_ne _ (by decide)]; exact h.killDeadline

theorem alB1_getStor (sevm : Sevm) (b : Devm) :
    (alB1 sevm b).getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set lockSlot 1 := by
  rw [alB1, afterSload_getStor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
    afterSload_getStor, lockSlot_lit]
  rfl

theorem xa_al_p1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {s : State} (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0xe55 (St b [] M G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧
    (B256.eqCheck ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] /
      (b.getStor sevm.currentTarget).get feeSlot) (Bytes.toB256 [3]) |||
      B256.eqCheck ((b.getStor sevm.currentTarget).get feeSlot) 0) ≠ 0 ∧
    ∃ (A : B256) (M1 : Mem) (img1 : Bytes) (G1 : Nat),
      aChk s sevm.benvStat.time.toNat = some A.toNat ∧ Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      WordAt img1 0x140 0 ∧ WordAt img1 0x160 0 ∧ WordAt img1 0x180 0 ∧
      WordAt img1 0x1a0 ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] /
        Bytes.toB256 [8]) ∧
      WordAt img1 0x1c0 ((b.getStor sevm.currentTarget).get adminFeeSlot) ∧
      WordAt img1 0x1e0 A ∧
      XAt sevm post 0xf0d (St (aBase sevm (alB1 sevm b)) [] M1 G1) L := by
  xs 0xe59 (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0xe5a (.reg .sload) ri_sload
  xs 0xe5b (.reg .iszero) ri_iszero
  xs 0xe5e (.push [0x0e, 0x63] (by decide)) ri_push
  xji 0xe5f 0xe63 hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xjd 0xe64
  xs 0xe66 (.push [0x01] (by decide)) ri_push
  xs 0xe6a (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0xe6b (.reg .sstore) ri_sstore
  xs 0xe6c (.reg .callvalue) ri_callvalue
  xs 0xe6d (.reg .iszero) ri_iszero
  xs 0xe70 (.push [0x0e, 0x75] (by decide)) ri_push
  xji 0xe71 0xe75 hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0xe76
  xs 0xe78 (.push [0x0f] (by decide)) ri_push
  xw 0xe79 (.reg .sload) ri_sload
  xs 0xe7a (.reg .iszero) ri_iszero
  xs 0xe7d (.push [0x0e, 0x82] (by decide)) ri_push
  xji 0xe7e 0xe82 hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [getStorVal_afterSstore_ne (by decide), getStorVal_eq, afterSload_getStor,
      isKilledSlot_lit] at e
    exact e
  clear hw
  xjd 0xe83
  xs 0xe85 (.push [0x60] (by decide)) ri_push
  xs 0xe86 (.reg .calldatasize) ri_calldatasize
  xs 0xe89 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0xe8a (.reg .calldatacopy) (ri_calldatacopy_imgAt (o := 0x140) (z := 0x60) rfl rfl)
  xs 0xe8c (.push [0x02] (by decide)) ri_push
  xw 0xe8d (.reg .sload) ri_sload
  rw [getStorVal_afterSload, getStorVal_afterSstore_ne (by decide), getStorVal_eq, afterSload_getStor, feeSlot_lit] at h
  xs 0xe8f (.push [0x03] (by decide)) ri_push
  xs 0xe90 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0xe91 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0xe92 (.reg .mul) ri_mul
  xs 0xe93 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0xe94 (.reg .iszero) ri_iszero
  xs 0xe95 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0xe96 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0xe97 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0xe98 (.reg .div) ri_div
  xs 0xe99 (.reg .eq) ri_eq
  xs 0xe9a (.reg .or) ri_or
  xs 0xe9d (.push [0x0e, 0xa2] (by decide)) ri_push
  xji 0xe9e 0xea2 hw
  · xdead
  have hmulw := hw
  clear hw
  xjd 0xea3
  xs 0xea4 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0xea5 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0xea6 (.reg .pop) ri_pop
  xs 0xea7 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0xea8 (.reg .pop) ri_pop
  xs 0xea9 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0xeaa (.reg .pop) ri_pop
  xs 0xeac (.push [0x08] (by decide)) ri_push
  xs 0xead (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0xeae (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0xeb1 (.push [0x0e, 0xb6] (by decide)) ri_push
  xji 0xeb2 0xeb6 hw
  · xdead
  clear hw
  xjd 0xeb7
  xs 0xeb8 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0xeb9 (.reg .div) ri_div
  xs 0xeba (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0xebb (.reg .pop) ri_pop
  xs 0xebc (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0xebd (.reg .pop) ri_pop
  xs 0xec0 (.push [0x01, 0xa0] (by decide)) ri_push
  xmo 0xec1 (.reg .mstore) (ri_mstore_imgAt (o := 0x1a0) rfl)
  xs 0xec3 (.push [0x03] (by decide)) ri_push
  xw 0xec4 (.reg .sload) ri_sload
  rw [getStorVal_afterSload, getStorVal_afterSload, getStorVal_afterSstore_ne (by decide), getStorVal_eq, afterSload_getStor, adminFeeSlot_lit] at h
  xs 0xec7 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0xec8 (.reg .mstore) (ri_mstore_imgAt (o := 0x1c0) rfl)
  xs 0xecb (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0xecc (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  xs 0xecf (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0xed0 (.reg .mload) (ri_mload_imgAt (o := 0x160) rfl)
  xs 0xed3 (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0xed4 (.reg .mload) (ri_mload_imgAt (o := 0x180) rfl)
  xs 0xed7 (.push [0x01, 0xa0] (by decide)) ri_push
  xmo 0xed8 (.reg .mload) (ri_mload_imgAt (o := 0x1a0) rfl)
  xs 0xedb (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0xedc (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  xs 0xedf (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0xee0 (.reg .mload) (ri_mload_imgAt (o := 0x1e0) rfl)
  have hZ : List.sliceD sevm.data (Nat.toB256 (List.length sevm.data)).toNat 96 0 =
      List.replicate 96 0 := by
    rw [B256.toNat_toB256_of_lt hcd]; exact List.sliceD_length_eq
  rw [hZ] at hR h
  have f0 : ∀ j, j < 3 → WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
      (List.replicate 96 0)) 0x1a0 ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] /
      Bytes.toB256 [8]).toBytes) 0x1c0 ((b.getStor sevm.currentTarget).get adminFeeSlot).toBytes)
      (0x140 + 32 * j) 0 := by
    intro j hj
    exact WordAt.write_other (WordAt.write_other (al_zeroWord _ (by omega))
      (by simp only [B256.length_toBytes]; omega)) (by simp only [B256.length_toBytes]; omega)
  rw [(f0 0 (by decide)).read, (f0 1 (by decide)).read, (f0 2 (by decide)).read,
    (WordAt.write_other (WordAt.write_self _ 0x1a0 ((b.getStor sevm.currentTarget).get feeSlot *
      Bytes.toB256 [3] / Bytes.toB256 [8])) (by simp only [B256.length_toBytes]; omega)).read,
    (WordAt.write_self _ 0x1c0 ((b.getStor sevm.currentTarget).get adminFeeSlot)).read] at h
  xs 0xee2 (.push [0x06] (by decide)) ri_push
  replace h := xa_al_pc (atN hcode (by kernel_rfl)) h
  obtain ⟨_, h⟩ := h
  xs 0xee4 (.reg .add) ri_add
  rw [show Nat.toB256 0xee2 + Bytes.toB256 [6] = Nat.toB256 0xee8 by decide] at h
  xs 0xee7 (.push [0x00, 0xa9] (by decide)) ri_push
  xjmp 0xa9
  have ha1 : Abstracts ((alB1 sevm b).getStor sevm.currentTarget) s := by
    rw [alB1_getStor]; exact al_abstracts_lock ha 1
  replace h : XAt sevm post 0xa9 (St (alB1 sevm b) _ _ _) L := h
  obtain ⟨A, M1, G1, hA, hk, hW1, -, h⟩ := xa_al_A hchk hcode hfork ha1 hW h
  obtain ⟨img1, hR1, hag⟩ := Mem.Reads.keepsOff hR hk
  clear hR hW hk
  have hR := hR1
  have hW := hW1
  clear hR1 hW1
  rw [show (Nat.toB256 0xee8).toNat = 0xee8 by decide] at h
  xjd 0xee9
  xs 0xeec (.push [0x02, 0x20] (by decide)) ri_push
  xmo 0xeed (.reg .mstore) (ri_mstore_imgAt (o := 0x220) rfl)
  xs 0xef0 (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0xef1 (.reg .mstore) (ri_mstore_imgAt (o := 0x1e0) rfl)
  xs 0xef4 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0xef5 (.reg .mstore) (ri_mstore_imgAt (o := 0x1c0) rfl)
  xs 0xef8 (.push [0x01, 0xa0] (by decide)) ri_push
  xmo 0xef9 (.reg .mstore) (ri_mstore_imgAt (o := 0x1a0) rfl)
  xs 0xefc (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0xefd (.reg .mstore) (ri_mstore_imgAt (o := 0x180) rfl)
  xs 0xf00 (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0xf01 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  xs 0xf04 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0xf05 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  obtain ⟨img2, hR2, hI⟩ := Mem.Reads.forget hR
  clear hR
  have hR := hR2
  clear hR2
  have g220 : WordAt img2 0x220 A := by rw [hI]; wchain
  xs 0xf08 (.push [0x02, 0x20] (by decide)) ri_push
  xmo 0xf09 (.reg .mload) (ri_mload_imgAt (o := 0x220) rfl)
  rw [g220.read] at h
  xs 0xf0c (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0xf0d (.reg .mstore) (ri_mstore_imgAt (o := 0x1e0) rfl)
  refine ⟨hlock, hval, hkill, hmulw, A, _, _, _, hA, hR, hW, ?_, ?_, ?_, ?_, ?_, WordAt.write_self _ _ _,
    h⟩ <;> refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega) <;> rw [hI] <;>
    wchain

end Blanc.Lift.Curve3Pool
