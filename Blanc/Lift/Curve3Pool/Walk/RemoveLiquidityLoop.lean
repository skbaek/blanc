import Blanc.Lift.Curve3Pool.Walk.Kit

/-!
# `remove_liquidity`, part 2: one iteration of the withdrawal loop, up to the transfer

From the loop head (`0x2cdb`, counter `i < 3` at `0x2a0`) to the coin's `transfer` call
(`0x2ed6`): `value = balances[i] * _amount / total_supply` (checked), the minimum check against
`min_amounts[i]`, `balances[i] -= value` (checked), `amounts[i] = value`, and the `transfer`
calldata built with two identity-precompile copies.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `transfer` payload's identity copy: the length word, then the selector, the receiver and
the value, as the four writes left them. -/
theorem transfer_copy (img : Bytes) (E C V : B256) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 1152 transferSel) 1156
      C.toBytes) 1188 V.toBytes) 1120 E.toBytes).sliceD 1120 100 0).take 100 =
      E.toBytes ++ (transferSel ++ C.toBytes ++ V.toBytes) := by
  refine Region.copy ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl)
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  refine Region.append' (o' := 1152) (Region.of_word (WordAt.write_self _ _ _))
    (Region.append' (o' := 1188) (Region.append' (o' := 1156) ?_ ?_ (by rfl)) ?_
      (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [B256.length_toBytes])
  · refine Region.write_other (Region.write_other (Region.write_other (Region.write_self _ _ _)
      ?_) ?_) ?_ <;> simp only [transferSel, B256.length_toBytes, List.length_cons,
        List.length_nil] <;> omega
  · refine Region.write_other (Region.of_word (WordAt.write_other (WordAt.write_self _ _ _) ?_))
      ?_ <;> simp only [B256.length_toBytes] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)

theorem keccak_zero (img : Bytes) :
    Bytes.keccak ((Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes).sliceD 0xc0 0x20 0) =
      coinsBase := by
  rw [show (0x20 : Nat) = (Bytes.toB256 [0]).toBytes.length from (B256.length_toBytes _).symm,
    Bytes.sliceD_writeAt, zero_lit, coinsBase_eq]

theorem coin_ne_bal {i : Nat} (hi : i < 3) :
    balancesBase + Nat.toB256 i ≠ coinsBase + Nat.toB256 i := by
  match i, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide

theorem lt_three {i : Nat} (hi : i < 3) : Nat.toB256 i < Bytes.toB256 [3] := by
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]
  exact hi

theorem one_lit : Bytes.toB256 [1] = 1 := by decide

theorem keccak_one (img : Bytes) :
    Bytes.keccak ((Bytes.writeAt img 0xc0 (Bytes.toB256 [1]).toBytes).sliceD 0xc0 0x20 0) =
      balancesBase := by
  rw [show (0x20 : Nat) = (Bytes.toB256 [1]).toBytes.length from (B256.length_toBytes _).symm,
    Bytes.sliceD_writeAt, one_lit, balancesBase_eq]

theorem off_amt {i : Nat} (hi : i < 3) :
    (Bytes.toB256 [0x20] * Nat.toB256 i + Bytes.toB256 [0x01, 0xe0]).toNat = 0x1e0 + 32 * i := by
  rw [B256.toNat_add, B256.toNat_mul, B256.toNat_toB256_of_lt (by omega)]
  show (32 * i % 2 ^ 256 + 480) % 2 ^ 256 = 480 + 32 * i
  omega

/-- The loop's memory at counter `i`: the counter, the supply word `T` and the six
amount/fee words `a`. -/
structure LoopImg (img : Bytes) (i : Nat) (T : B256) (a : Nat → B256) : Prop where
  ctr : WordAt img 0x2a0 (Nat.toB256 i)
  supply : WordAt img 0x140 T
  amt : ∀ j, j < 6 → WordAt img (0x1e0 + 32 * j) (a j)

/-- `balances[i]` in `σ`. -/
abbrev balAt (σ : Stor) (i : Nat) : B256 := σ.get (balancesBase + Nat.toB256 i)

/-- `coins[i]` in `σ`. -/
abbrev coinAt (σ : Stor) (i : Nat) : B256 := σ.get (coinsBase + Nat.toB256 i)

/-- `_amount`, the burned share. -/
abbrev rlAmt (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4])

/-- `min_amounts[i]`. -/
abbrev rlMin (sevm : Sevm) (i : Nat) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 i + Bytes.toB256 [36])

/-- The withdrawn `value = balances[i] * _amount / total_supply`. -/
abbrev rlVal (sevm : Sevm) (σ : Stor) (T : B256) (i : Nat) : B256 := balAt σ i * rlAmt sevm / T


/-- **Segment 1** (`0x2cdb` → `0x2e12`): the counter test, `value = balances[i] * _amount /
total_supply` with its checks, `min_amounts[i] ≤ value`, `balances[i] -= value`, and
`amounts[i] = value`. -/
theorem xa_rl_s1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {σ : Stor} {i : Nat} {T : B256} {a : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hL : LoopImg img i T a)
    (hstor : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (h : XAt sevm post 0x2cdb (St b [3, 0x2a0] M G) L) :
    (balAt σ i * rlAmt sevm / balAt σ i = rlAmt sevm ∨ balAt σ i = 0) ∧ T ≠ 0 ∧
      ¬ rlVal sevm σ T i < rlMin sevm i ∧ ¬ balAt σ i < rlVal sevm σ T i ∧
      ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧
        LoopImg img' i T (Function.update a i (rlVal sevm σ T i)) ∧
        WordAt img' 0x2c0 (rlVal sevm σ T i) ∧
        XAt sevm post 0x2e12 (St (afterSstore sevm (afterSload sevm (afterSload sevm b
          (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i))
          (balancesBase + Nat.toB256 i) (balAt σ i - rlVal sevm σ T i)) [3, 0x2a0] M' G') L := by
  have hctr := hL.ctr
  have hT := hL.supply
  xjd 0x2cdc
  xs 0x2cdf (.push [0x02, 0xa0] (by decide)) ri_push
  xmo 0x2ce0 (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  rw [hctr.read] at h
  xs 0x2ce2 (.push [0x03] (by decide)) ri_push
  xs 0x2ce3 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2ce4 (.reg .lt) ri_lt
  xs 0x2ce7 (.push [0x2c, 0xec] (by decide)) ri_push
  xji 0x2ce8 0x2cec hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x2ced
  xs 0x2cef (.push [0x01] (by decide)) ri_push
  xs 0x2cf1 (.push [0xc0] (by decide)) ri_push
  xmo 0x2cf2 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x2cf4 (.push [0x20] (by decide)) ri_push
  xs 0x2cf6 (.push [0xc0] (by decide)) ri_push
  xmo 0x2cf7 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x2cf8 (.reg .add) ri_add
  xw 0x2cf9 (.reg .sload) ri_sload
  rw [getStorVal_eq, hstor] at h
  xs 0x2cfb (.push [0x04] (by decide)) ri_push
  xs 0x2cfc (.reg .calldataload) ri_calldataload
  xs 0x2cfd (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2cfe (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2cff (.reg .mul) ri_mul
  xs 0x2d00 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2d01 (.reg .iszero) ri_iszero
  xs 0x2d02 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2d03 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2d04 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x2d05 (.reg .div) ri_div
  xs 0x2d06 (.reg .eq) ri_eq
  xs 0x2d07 (.reg .or) ri_or
  xs 0x2d0a (.push [0x2d, 0x0f] (by decide)) ri_push
  xji 0x2d0b 0x2d0f hmul
  · xdead
  xjd 0x2d10
  xs 0x2d11 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2d12 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2d13 (.reg .pop) ri_pop
  xs 0x2d14 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2d15 (.reg .pop) ri_pop
  xs 0x2d16 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2d17 (.reg .pop) ri_pop
  xs 0x2d1a (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x2d1b (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hT.read] at h
  xs 0x2d1c (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2d1d (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2d20 (.push [0x2d, 0x25] (by decide)) ri_push
  xji 0x2d21 0x2d25 hT0
  · xdead
  xjd 0x2d26
  xs 0x2d27 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2d28 (.reg .div) ri_div
  xs 0x2d29 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2d2a (.reg .pop) ri_pop
  xs 0x2d2b (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2d2c (.reg .pop) ri_pop
  xs 0x2d2f (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x2d30 (.reg .mstore) (ri_mstore_imgAt (o := 0x2c0) rfl)
  xs 0x2d35 (.push [0x08, 0xc3, 0x79, 0xa0] (by decide)) ri_push
  xs 0x2d38 (.push [0x02, 0xe0] (by decide)) ri_push
  xmo 0x2d39 (.reg .mstore) (ri_mstore_imgAt (o := 0x2e0) rfl)
  xs 0x2d3b (.push [0x20] (by decide)) ri_push
  xs 0x2d3e (.push [0x03, 0x00] (by decide)) ri_push
  xmo 0x2d3f (.reg .mstore) (ri_mstore_imgAt (o := 0x300) rfl)
  xs 0x2d41 (.push [0x30] (by decide)) ri_push
  xs 0x2d44 (.push [0x03, 0x20] (by decide)) ri_push
  xmo 0x2d45 (.reg .mstore) (ri_mstore_imgAt (o := 0x320) rfl)
  xs 0x2d66 (.push [0x57, 0x69, 0x74, 0x68, 0x64, 0x72, 0x61, 0x77, 0x61, 0x6c, 0x20, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x65, 0x64, 0x20, 0x69, 0x6e, 0x20, 0x66, 0x65, 0x77, 0x65, 0x72, 0x20, 0x63, 0x6f, 0x69] (by decide)) ri_push
  xs 0x2d69 (.push [0x03, 0x40] (by decide)) ri_push
  xmo 0x2d6a (.reg .mstore) (ri_mstore_imgAt (o := 0x340) rfl)
  xs 0x2d8b (.push [0x6e, 0x73, 0x20, 0x74, 0x68, 0x61, 0x6e, 0x20, 0x65, 0x78, 0x70, 0x65, 0x63, 0x74, 0x65, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x2d8e (.push [0x03, 0x60] (by decide)) ri_push
  xmo 0x2d8f (.reg .mstore) (ri_mstore_imgAt (o := 0x360) rfl)
  xs 0x2d92 (.push [0x03, 0x20] (by decide)) ri_push
  xs 0x2d93 (.reg .pop) ri_pop
  xs 0x2d95 (.push [0x24] (by decide)) ri_push
  xs 0x2d98 (.push [0x02, 0xa0] (by decide)) ri_push
  xmo 0x2d99 (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read] at h
  xs 0x2d9b (.push [0x03] (by decide)) ri_push
  xs 0x2d9c (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2d9d (.reg .lt) ri_lt
  xs 0x2da0 (.push [0x2d, 0xa5] (by decide)) ri_push
  xji 0x2da1 0x2da5 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x2da6
  xs 0x2da8 (.push [0x20] (by decide)) ri_push
  xs 0x2da9 (.reg .mul) ri_mul
  xs 0x2daa (.reg .add) ri_add
  xs 0x2dab (.reg .calldataload) ri_calldataload
  xs 0x2dae (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x2daf (.reg .mload) (ri_mload_imgAt (o := 0x2c0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self] at h
  xs 0x2db0 (.reg .lt) ri_lt
  xs 0x2db1 (.reg .iszero) ri_iszero
  xs 0x2db4 (.push [0x2d, 0xbb] (by decide)) ri_push
  xji 0x2db5 0x2dbb hmin
  · xs 0x2db7 (.push [0x84] (by decide)) ri_push
    xs 0x2dba (.push [0x02, 0xfc] (by decide)) ri_push
    xrevert
  xjd 0x2dbc
  xs 0x2dbf (.push [0x02, 0xa0] (by decide)) ri_push
  xmo 0x2dc0 (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read] at h
  xs 0x2dc2 (.push [0x03] (by decide)) ri_push
  xs 0x2dc3 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2dc4 (.reg .lt) ri_lt
  xs 0x2dc7 (.push [0x2d, 0xcc] (by decide)) ri_push
  xji 0x2dc8 0x2dcc hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x2dcd
  xs 0x2dcf (.push [0x01] (by decide)) ri_push
  xs 0x2dd1 (.push [0xc0] (by decide)) ri_push
  xmo 0x2dd2 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x2dd4 (.push [0x20] (by decide)) ri_push
  xs 0x2dd6 (.push [0xc0] (by decide)) ri_push
  xmo 0x2dd7 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x2dd8 (.reg .add) ri_add
  xs 0x2dd9 (.reg (.dup 0)) (ri_dup (by rfl))
  xw 0x2dda (.reg .sload) ri_sload
  rw [getStorVal_afterSload, getStorVal_eq, hstor] at h
  xs 0x2ddd (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x2dde (.reg .mload) (ri_mload_imgAt (o := 0x2c0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self] at h
  xs 0x2ddf (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2de0 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2de1 (.reg .lt) ri_lt
  xs 0x2de2 (.reg .iszero) ri_iszero
  xs 0x2de5 (.push [0x2d, 0xea] (by decide)) ri_push
  xji 0x2de6 0x2dea hle
  · xdead
  xjd 0x2deb
  xs 0x2dec (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2ded (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2dee (.reg .sub) ri_sub
  xs 0x2def (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2df0 (.reg .pop) ri_pop
  xs 0x2df1 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2df2 (.reg .pop) ri_pop
  xs 0x2df3 (.reg (.dup 1)) (ri_dup (by rfl))
  xw 0x2df4 (.reg .sstore) ri_sstore
  xs 0x2df5 (.reg .pop) ri_pop
  xs 0x2df8 (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x2df9 (.reg .mload) (ri_mload_imgAt (o := 0x2c0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self] at h
  xs 0x2dfc (.push [0x01, 0xe0] (by decide)) ri_push
  xs 0x2dff (.push [0x02, 0xa0] (by decide)) ri_push
  xmo 0x2e00 (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, hctr.read] at h
  xs 0x2e02 (.push [0x03] (by decide)) ri_push
  xs 0x2e03 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2e04 (.reg .lt) ri_lt
  xs 0x2e07 (.push [0x2e, 0x0c] (by decide)) ri_push
  xji 0x2e08 0x2e0c hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x2e0d
  xs 0x2e0f (.push [0x20] (by decide)) ri_push
  xs 0x2e10 (.reg .mul) ri_mul
  xs 0x2e11 (.reg .add) ri_add
  xmo 0x2e12 (.reg .mstore) (ri_mstore_imgAt (o := 0x1e0 + 32 * i) (off_amt hi))
  have hmul' := or_ne_zero hmul
  refine ⟨hmul'.imp eqCheck_ne_zero eqCheck_ne_zero, hT0,
    ltCheck_eq_zero (eqCheck_ne_zero hmin), ltCheck_eq_zero (eqCheck_ne_zero hle),
    _, _, _, hR, hW, ⟨?_, ?_, ?_⟩, ?_, h⟩
  · wchainT; exact hctr
  · wchainT; exact hT
  · intro j hj
    by_cases e : j = i
    · subst e; rw [Function.update_self]; wchainT
    · rw [Function.update_of_ne e]; wchainT; exact hL.amt j hj
  · wchainT

/-- **Segment 2** (`0x2e12` → `0x2eaa`): the `transfer` payload, built with two identity copies
(the first unchecked, so a failure there leaves no gas). -/
theorem xa_rl_s2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {T v : B256} {a : Nat → B256}
    (hcode : sevm.code = code) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hL : LoopImg img i T a)
    (hv : WordAt img 0x2c0 v) (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (h : XAt sevm post 0x2e12 (St b [3, 0x2a0] M G) L) :
    ∃ b' M' img' G', BaseRel b b' ∧ Mem.Reads M' img' ∧ Mem.Wf M' ∧ LoopImg img' i T a ∧
      Region img' 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes)) ∧
      XAt sevm post 0x2eaa (St b' [3, 0x2a0] M' G') L := by
  xs 0x2e14 (.push [0x00] (by decide)) ri_push
  xs 0x2e16 (.push [0x04] (by decide)) ri_push
  xs 0x2e19 (.push [0x04, 0x00] (by decide)) ri_push
  xmo 0x2e1a (.reg .mstore) (ri_mstore_imgAt (o := 0x400) rfl)
  xs 0x2e3b (.push [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x2e3e (.push [0x04, 0x20] (by decide)) ri_push
  xmo 0x2e3f (.reg .mstore) (ri_mstore_imgAt (o := 0x420) rfl)
  xs 0x2e42 (.push [0x04, 0x00] (by decide)) ri_push
  xs 0x2e44 (.push [0x04] (by decide)) ri_push
  xs 0x2e45 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2e47 (.push [0x20] (by decide)) ri_push
  xs 0x2e48 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2e4b (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x2e4c (.reg .add) ri_add
  xs 0x2e4d (.reg .add) ri_add
  xs 0x2e4e (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2e50 (.push [0x20] (by decide)) ri_push
  xs 0x2e51 (.reg (.dup 5)) (ri_dup (by rfl))
  xs 0x2e52 (.reg .add) ri_add
  xs 0x2e54 (.push [0x00] (by decide)) ri_push
  xs 0x2e56 (.push [0x04] (by decide)) ri_push
  xs 0x2e57 (.reg .gas) ri_gas_remaining
  have e1 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img1, hR, hI⟩ := e1
  have f_ctr : WordAt img1 0x2a0 (Nat.toB256 i) := by rw [hI]; wchainT; exact hL.ctr
  have f_T : WordAt img1 0x140 T := by rw [hI]; wchainT; exact hL.supply
  have f_v : WordAt img1 0x2c0 v := by rw [hI]; wchainT; exact hv
  have f_400 : WordAt img1 0x400 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0x420 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  have f_amt : ∀ j, j < 6 → WordAt img1 (0x1e0 + 32 * j) (a j) := by
    intro j hj; rw [hI]; wchainT; exact hL.amt j hj
  clear hI hL hv
  replace h := xa_identity_img (pc' := 0x2e58) (i := 0x420) (n := 4) (o := 0x480) (z := 4) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  have hsel4 : (img1.sliceD 0x420 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel _ b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  xs 0x2e59 (.reg .pop) ri_pop
  xs 0x2e5a (.reg .pop) ri_pop
  xs 0x2e5b (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x2e5c (.reg .mload) (ri_mload_imgAt (o := 0x400) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_400.read] at h
  xs 0x2e5d (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2e5e (.reg .add) ri_add
  xs 0x2e5f (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x2e60 (.reg .pop) ri_pop
  xs 0x2e61 (.reg .pop) ri_pop
  xs 0x2e62 (.reg .caller) ri_caller
  xs 0x2e64 (.push [0x20] (by decide)) ri_push
  xs 0x2e65 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2e68 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x2e69 (.reg .add) ri_add
  xs 0x2e6a (.reg .add) ri_add
  xmo 0x2e6b (.reg .mstore) (ri_mstore_imgAt (o := 0x484) (by decide))
  xs 0x2e6d (.push [0x20] (by decide)) ri_push
  xs 0x2e6e (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2e6f (.reg .add) ri_add
  xs 0x2e70 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2e71 (.reg .pop) ri_pop
  xs 0x2e74 (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x2e75 (.reg .mload) (ri_mload_imgAt (o := 0x2c0) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read] at h
  xs 0x2e77 (.push [0x20] (by decide)) ri_push
  xs 0x2e78 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2e7b (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x2e7c (.reg .add) ri_add
  xs 0x2e7d (.reg .add) ri_add
  xmo 0x2e7e (.reg .mstore) (ri_mstore_imgAt (o := 0x4a4) (by decide))
  xs 0x2e80 (.push [0x20] (by decide)) ri_push
  xs 0x2e81 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2e82 (.reg .add) ri_add
  xs 0x2e83 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2e84 (.reg .pop) ri_pop
  xs 0x2e85 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2e88 (.push [0x04, 0x60] (by decide)) ri_push
  xmo 0x2e89 (.reg .mstore) (ri_mstore_imgAt (o := 0x460) rfl)
  xs 0x2e8c (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x2e8d (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2e8e (.reg .pop) ri_pop
  xs 0x2e8f (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x2e90 (.reg .mload) (ri_mload_imgAt (o := 0x460) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x2e92 (.push [0x20] (by decide)) ri_push
  xs 0x2e93 (.reg .add) ri_add
  xs 0x2e94 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2e97 (.push [0x05, 0x00] (by decide)) ri_push
  xs 0x2e98 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2e99 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2e9b (.push [0x00] (by decide)) ri_push
  xs 0x2e9d (.push [0x04] (by decide)) ri_push
  xs 0x2e9e (.reg .gas) ri_gas_remaining
  replace h := xa_identity_img (pc' := 0x2e9f) (i := 0x460) (n := 0x64) (o := 0x500) (z := 0x64) (hid.of_rel hb12)
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L2, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b3, G3, M, hsha2, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x2ea2 (.push [0x2e, 0xa7] (by decide)) ri_push
    xji 0x2ea3 0x2ea7 hw
    · xdead
    · exact absurd rfl hw
  rw [transfer_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2
  have e3 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img3, hR, hI⟩ := e3
  have g_ctr : WordAt img3 0x2a0 (Nat.toB256 i) := by
    rw [hI]; wchainT; exact f_ctr
  have g_T : WordAt img3 0x140 T := by rw [hI]; wchainT; exact f_T
  have g_amt : ∀ j, j < 6 → WordAt img3 (0x1e0 + 32 * j) (a j) := by
    intro j hj; rw [hI]; wchainT; exact f_amt j hj
  have g_data : Region img3 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++
        v.toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI f_ctr f_T f_amt f_v f_400 f_sel
  xs 0x2ea2 (.push [0x2e, 0xa7] (by decide)) ri_push
  xji 0x2ea3 0x2ea7 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x2ea8
  xs 0x2ea9 (.reg .pop) ri_pop
  xs 0x2eaa (.reg .pop) ri_pop
  exact ⟨b3, M, img3, _, hb12.trans hb23, hR, hW, ⟨g_ctr, g_T, g_amt⟩, g_data, h⟩


/-- **Segment 3** (`0x2eaa` → `0x2edf`): `coins[i]` and the `transfer` `CALL` with value `0`,
input the payload's last `0x44` bytes, output window `0x5c0`; a zero flag reverts. -/
theorem xa_rl_s3 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} {v cw : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hctr : WordAt img 0x2a0 (Nat.toB256 i))
    (hdata : Region img 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes)))
    (hcw : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = cw)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp cw.toAdr)
    (h : XAt sevm post 0x2eaa (St b [3, 0x2a0] M G) L) :
    ∃ c L' d G', L = c :: L' ∧
      ChildOf b d cw.toAdr (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes) 0
        sevm.isStatic c ∧
      Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0
        (d.returnData.take 0x20)) ∧ Mem.Wf d.memory ∧ d.returnData.length < 2 ^ 256 ∧
      XAt sevm post 0x2ee0 (St d [3, 0x2a0] d.memory G') L' := by
  xs 0x2eac (.push [0x20] (by decide)) ri_push
  xs 0x2eaf (.push [0x05, 0xc0] (by decide)) ri_push
  xs 0x2eb2 (.push [0x05, 0x00] (by decide)) ri_push
  xmo 0x2eb3 (.reg .mload) (ri_mload_imgAt (o := 0x500) rfl)
  rw [(Region.word hdata.left).read] at h
  xs 0x2eb6 (.push [0x05, 0x20] (by decide)) ri_push
  xs 0x2eb8 (.push [0x00] (by decide)) ri_push
  xs 0x2ebb (.push [0x02, 0xa0] (by decide)) ri_push
  xmo 0x2ebc (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  rw [hctr.read] at h
  xs 0x2ebe (.push [0x03] (by decide)) ri_push
  xs 0x2ebf (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2ec0 (.reg .lt) ri_lt
  xs 0x2ec3 (.push [0x2e, 0xc8] (by decide)) ri_push
  xji 0x2ec4 0x2ec8 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt (lt_three hi))
  clear hw
  xjd 0x2ec9
  xs 0x2ecb (.push [0x00] (by decide)) ri_push
  xs 0x2ecd (.push [0xc0] (by decide)) ri_push
  xmo 0x2ece (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x2ed0 (.push [0x20] (by decide)) ri_push
  xs 0x2ed2 (.push [0xc0] (by decide)) ri_push
  xmo 0x2ed3 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x2ed4 (.reg .add) ri_add
  xw 0x2ed5 (.reg .sload) ri_sload
  rw [getStorVal_eq, hcw] at h
  xs 0x2ed6 (.reg .gas) ri_gas_remaining
  have hin : (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes).sliceD 0x520 0x44 0 =
      transferSel ++ sevm.caller.toB256.toBytes ++ (v).toBytes := by
    refine Region.slice (Region.write_other hdata.right (by simp only [B256.length_toBytes]; omega))
      (by simp only [List.length_append, B256.length_toBytes]; rfl)
  replace h := xa_call_img (pc' := 0x2ed7) (i := 0x520) (n := 0x44) (o := 0x5c0) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d4, flag, L4, h, hrd4, hk⟩ := h
  rw [hin] at hk
  xs 0x2eda (.push [0x2e, 0xdf] (by decide)) ri_push
  xji 0x2edb 0x2edf hw
  · xdead
  obtain ⟨hR, hW, hout4, hch⟩ := hk hw
  clear hk hin hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  xjd 0x2ee0
  refine ⟨c, L4, d4, _, rfl, ?_, hR, hW, hrd4, h⟩
  have e0 : Bytes.toB256 [0] = 0 := zero_lit
  rw [e0] at hc
  exact hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
    (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _)

/-- **Segment 4** (`0x2ee0` → `0x2f6b`): Vyper's `raw_call(…, max_outsize=32)` success test
after the `transfer` call (`len = min(RETURNDATASIZE, 32)` at `0x5a0`, the checked identity copy
of `0x5a0[0 : 32 + len]` to `0x3a0`, and the `len > 0` conversion test): the returned data
passes `RawCallOk`. -/
theorem xa_rl_s4 {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hid : IdReady sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0x5c0 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x2ee0 (St d [3, 0x2a0] M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x3a0 ∨ 0x3e0 ≤ o) →
        (o + 32 ≤ 0x5a0 ∨ 0x5e0 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x2f6b (St b6 [3, 0x2a0] M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x2ef3 (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        [3, 0x2a0]) M G5) L := by
    xs 0x2ee2 (.push [0x20] (by decide)) ri_push
    xs 0x2ee3 (.reg .returndatasize) ri_returndatasize
    xs 0x2ee4 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x2ee5 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x2ee6 (.reg .gt) ri_gt
    xs 0x2ee7 (.reg .iszero) ri_iszero
    xs 0x2eea (.push [0x2e, 0xf0] (by decide)) ri_push
    xji 0x2eeb 0x2ef0 hw
    · xs 0x2eec (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2eef (.push [0x2e, 0xf2] (by decide)) ri_push
      xjmp 0x2ef2
      xjd 0x2ef3
      refine ⟨_, _, ?_, h⟩
      have hlt := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x2ef1
      xs 0x2ef2 (.reg (.dup 1)) (ri_dup (by rfl))
      xjd 0x2ef3
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xs 0x2ef4 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2ef5 (.reg .pop) ri_pop
  xs 0x2ef6 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2ef7 (.reg .pop) ri_pop
  xs 0x2efa (.push [0x05, 0xa0] (by decide)) ri_push
  xmo 0x2efb (.reg .mstore) (ri_mstore_imgAt (o := 0x5a0) rfl)
  xs 0x2efe (.push [0x05, 0xa0] (by decide)) ri_push
  xs 0x2eff (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x2f00 (.reg .mload) (ri_mload_imgAt (o := 0x5a0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x2f02 (.push [0x20] (by decide)) ri_push
  xs 0x2f03 (.reg .add) ri_add
  xs 0x2f04 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2f07 (.push [0x03, 0xa0] (by decide)) ri_push
  xs 0x2f08 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2f09 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2f0b (.push [0x00] (by decide)) ri_push
  xs 0x2f0d (.push [0x04] (by decide)) ri_push
  xs 0x2f0e (.reg .gas) ri_gas_remaining
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_img (pc' := 0x2f0f) (i := 0x5a0) (n := 32 + (d.returnData.take 32).length)
    (o := 0x3a0) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW h
  clear hR hW
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x2f12 (.push [0x2f, 0x17] (by decide)) ri_push
    xji 0x2f13 0x2f17 hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0x5c0 (d.returnData.take 32)) 0x5a0
      nW.toBytes) 0x5a0 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0x5c0) (Region.write_self _ _ _)
      (Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega))
      (by simp only [B256.length_toBytes])
  rw [Region.copy r5 (by simp only [List.length_append, B256.length_toBytes])
    (by simp only [List.length_append, B256.length_toBytes])] at hR
  have hb46 : BaseRel d b6 :=
    ⟨hsha3.stor, hsha3.code, hsha3.addrs, hsha3.logs, hsha3.output, hsha3.error⟩
  clear hsha3 r5
  have e6 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img6, hR, hI⟩ := e6
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x3a0 ∨ 0x3e0 ≤ o) →
      (o + 32 ≤ 0x5a0 ∨ 0x5e0 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x3a0 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x2f12 (.push [0x2f, 0x17] (by decide)) ri_push
  xji 0x2f13 0x2f17 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x2f18
  xs 0x2f19 (.reg .pop) ri_pop
  xs 0x2f1a (.reg .pop) ri_pop
  have kr : Region img6 0x3c0 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x3a0 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x2f6b (St b6 [3, 0x2a0] M7 G7) L := by
    xs 0x2f1c (.push [0x00] (by decide)) ri_push
    xs 0x2f1f (.push [0x03, 0xa0] (by decide)) ri_push
    xmo 0x2f20 (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
    rw [kn.read] at h
    xs 0x2f21 (.reg .gt) ri_gt
    xs 0x2f22 (.reg .iszero) ri_iszero
    xs 0x2f25 (.push [0x2f, 0x6a] (by decide)) ri_push
    xji 0x2f26 0x2f6a hw
    · have hpos := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xs 0x2f29 (.push [0x03, 0xa0] (by decide)) ri_push
      xs 0x2f2a (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2f2c (.push [0x20] (by decide)) ri_push
      xs 0x2f2d (.reg .add) ri_add
      xmo 0x2f2e (.reg .mload) (ri_mload_imgAt (o := 0x3c0) (by decide))
      xs 0x2f30 (.push [0x00] (by decide)) ri_push
      xs 0x2f31 (.reg (.dup 2)) (ri_dup (by rfl))
      xmo 0x2f32 (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
      rw [kn.read] at h
      xs 0x2f33 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2f35 (.push [0x20] (by decide)) ri_push
      xs 0x2f36 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x2f37 (.reg .sgt) ri_sgt
      xs 0x2f38 (.reg .iszero) ri_iszero
      xs 0x2f3b (.push [0x2f, 0x40] (by decide)) ri_push
      xji 0x2f3c 0x2f40 hw
      · xdead
      clear hw
      xjd 0x2f41
      xs 0x2f42 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2f43 (.reg (.swap 1)) (ri_swap (by rfl))
      xs 0x2f44 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x2f45 (.reg .slt) ri_slt
      xs 0x2f46 (.reg .iszero) ri_iszero
      xs 0x2f49 (.push [0x2f, 0x4e] (by decide)) ri_push
      xji 0x2f4a 0x2f4e hw
      · xdead
      clear hw
      xjd 0x2f4f
      xs 0x2f50 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x2f52 (.push [0x20] (by decide)) ri_push
      xs 0x2f53 (.reg .sub) ri_sub
      xs 0x2f56 (.push [0x01, 0x00] (by decide)) ri_push
      xs 0x2f57 (.reg .exp) ri_exp
      xs 0x2f58 (.reg (.dup 2)) (ri_dup (by rfl))
      xs 0x2f59 (.reg .div) ri_div
      xs 0x2f5a (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2f5b (.reg .pop) ri_pop
      xs 0x2f5c (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2f5d (.reg .pop) ri_pop
      xs 0x2f5e (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x2f5f (.reg .pop) ri_pop
      xs 0x2f60 (.reg .iszero) ri_iszero
      xs 0x2f61 (.reg .iszero) ri_iszero
      xs 0x2f64 (.push [0x2f, 0x69] (by decide)) ri_push
      xji 0x2f65 0x2f69 hq
      · xdead
      xjd 0x2f6a
      xjd 0x2f6b
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := eqCheck_eq_zero (eqCheck_ne_zero hq)
      have hxs : (img6.sliceD 0x3c0 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hz
      xjd 0x2f6b
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩

theorem succ_lit {i : Nat} (hi : i < 3) : Bytes.toB256 [1] + Nat.toB256 i = Nat.toB256 (i + 1) := by
  match i, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide

/-- **Segment 5** (`0x2f6b` → the loop head or its exit): `i += 1`, back to `0x2cdb` unless
`i == 3`. -/
theorem xa_rl_s5 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {i : Nat} (hcode : sevm.code = code) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hctr : WordAt img 0x2a0 (Nat.toB256 i))
    (h : XAt sevm post 0x2f6b (St b [3, 0x2a0] M G) L) :
    ∃ M' G', Mem.Reads M' (Bytes.writeAt img 0x2a0 (Nat.toB256 (i + 1)).toBytes) ∧ Mem.Wf M' ∧
      XAt sevm post (if i + 1 = 3 then 0x2f7b else 0x2cdb) (St b [3, 0x2a0] M' G') L := by
  xjd 0x2f6c
  xs 0x2f6d (.reg (.dup 1)) (ri_dup (by rfl))
  xmo 0x2f6e (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  rw [hctr.read] at h
  xs 0x2f70 (.push [0x01] (by decide)) ri_push
  xs 0x2f71 (.reg .add) ri_add
  rw [succ_lit hi] at h
  xs 0x2f72 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2f73 (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x2f74 (.reg .mstore) (ri_mstore_imgAt (o := 0x2a0) rfl)
  xs 0x2f75 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2f76 (.reg .eq) ri_eq
  xs 0x2f77 (.reg .iszero) ri_iszero
  xs 0x2f7a (.push [0x2c, 0xdb] (by decide)) ri_push
  xji 0x2f7b 0x2cdb hw
  · have e : i + 1 = 3 := by
      have := eqCheck_ne_zero (eqCheck_eq_zero hw)
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact absurd this (by decide)
      · exact absurd this (by decide)
      · rfl
    split
    next => exact ⟨_, _, hR, hW, h⟩
    next he => exact absurd e he
  · have e : i + 1 ≠ 3 := by
      have := eqCheck_eq_zero (eqCheck_ne_zero hw)
      intro e; apply this; rw [show i = 2 by omega]; decide
    split
    next he => exact absurd he e
    next => exact ⟨_, _, hR, hW, h⟩

/-- **One iteration of the withdrawal loop**, from the loop head with counter `i < 3`: the
model's checks on `value = balances[i] * _amount / total_supply`, the next remaining child is
`coins[i].transfer(msg.sender, value)` with value `0` and returned data passing `RawCallOk`,
the pool's storage is `σ` with `balances[i] -= value`, the frame's logs gained exactly the
child's, and the loop continues at counter `i + 1` with `amounts[i] = value`. -/
theorem xa_rl_iter {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {σ : Stor} {i : Nat} {T : B256} {a : Nat → B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hL : LoopImg img i T a)
    (hstor : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp (coinAt σ i).toAdr)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0x2cdb (St b [3, 0x2a0] M G) L) :
    (balAt σ i * rlAmt sevm / balAt σ i = rlAmt sevm ∨ balAt σ i = 0) ∧ T ≠ 0 ∧
      ¬ rlVal sevm σ T i < rlMin sevm i ∧ ¬ balAt σ i < rlVal sevm σ T i ∧
      ∃ c L' b' M' img' G', L = c :: L' ∧
        c.sevm.currentTarget = (coinAt σ i).toAdr ∧
        c.sevm.data = transferSel ++ sevm.caller.toB256.toBytes ++ (rlVal sevm σ T i).toBytes ∧
        c.sevm.value = 0 ∧ c.sevm.isStatic = sevm.isStatic ∧ RawCallOk c.post.output ∧
        (∀ x, (b'.getStor sevm.currentTarget).get x =
          (σ.set (balancesBase + Nat.toB256 i) (balAt σ i - rlVal sevm σ T i)).get x) ∧
        b'.logs = b.logs ++ c.post.logs ∧ b'.output = b.output ∧
        b'.getCode sevm.currentTarget = b.getCode sevm.currentTarget ∧ IdReady sevm b' ∧
        Mem.Reads M' img' ∧ Mem.Wf M' ∧
        LoopImg img' (i + 1) T (Function.update a i (rlVal sevm σ T i)) ∧
        XAt sevm post (if i + 1 = 3 then 0x2f7b else 0x2cdb) (St b' [3, 0x2a0] M' G') L' := by
  obtain ⟨hmul, hT0, hmin, hle, M1, img1, G1, hR1, hW1, hL1, hv1, h1⟩ :=
    xa_rl_s1 hcode hfork hi hR hW hL hstor h
  have hid1 := ((hid.afterSload (balancesBase + Nat.toB256 i)).afterSload
    (balancesBase + Nat.toB256 i)).afterSstore (balancesBase + Nat.toB256 i)
    (balAt σ i - rlVal sevm σ T i)
  obtain ⟨b3, M3, img3, G3, hb13, hR3, hW3, hL3, hdata, h3⟩ :=
    xa_rl_s2 hcode hR1 hW1 hL1 hv1 hid1 hdepth h1
  have hs3 : ∀ x, (b3.getStor sevm.currentTarget).get x =
      (σ.set (balancesBase + Nat.toB256 i) (balAt σ i - rlVal sevm σ T i)).get x := by
    intro x
    rw [hb13.stor, afterSstore_getStor_self, afterSload_getStor, afterSload_getStor,
      Stor.get_set_ite, Stor.get_set_ite, hstor]
  have hcw : (b3.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = coinAt σ i := by
    rw [hs3, Stor.get_set_ne _ (coin_ne_bal hi)]
  obtain ⟨c, L', d, G4, rfl, hc, hR4, hW4, hrd, h4⟩ :=
    xa_rl_s3 hcode hfork hi hR3 hW3 hL3.ctr hdata hcw hcoin h3
  have hcode3 : b3.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [hb13.code, afterSstore_getCode, afterSload_getCode, afterSload_getCode]
  have hpc3 : b3.getCode sevm.currentTarget ≠ .empty := by rw [hcode3]; exact hpc
  have hid3 := hid1.of_rel hb13
  have hidd : IdReady sevm d :=
    ⟨by rw [hc.codePost, hidk c (List.mem_cons_self ..), hc.codePre]; exact hid3.nodeleg,
      hc.warm _ hid3.warm, hid.pre, hid.fork⟩
  obtain ⟨hok, b6, M6, img6, G6, hb6, hR6, hW6, hk6, h6⟩ := xa_rl_s4 hcode hidd hR4 hW4 hrd h4
  have hw4 : ∀ o w, WordAt img3 o w → o + 32 ≤ 0xc0 ∨ 0xe0 ≤ o → (o + 32 ≤ 0x3a0 ∨ 0x3e0 ≤ o) →
      (o + 32 ≤ 0x5a0 ∨ 0x5e0 ≤ o) → WordAt img6 o w := fun o w hw h0 h1 h2 =>
    hk6 o w (hw.write_other (by simp only [B256.length_toBytes]; omega)) h1 h2
  obtain ⟨M7, G7, hR7, hW7, h7⟩ := xa_rl_s5 hcode hi hR6 hW6
    (hw4 _ _ hL3.ctr (by omega) (by omega) (by omega)) h6
  refine ⟨hmul, hT0, hmin, hle, c, L', b6, M7, _, G7, rfl, hc.target, hc.data, hc.value,
    hc.isStatic, hc.output ▸ hok, ?_, ?_, ?_, ?_, hidd.of_rel hb6, hR7, hW7, ⟨?_, ?_, ?_⟩, h7⟩
  · intro x
    rw [hb6.stor, hc.storPost _ hpc3 x, hkeep c (List.mem_cons_self ..) x, hc.storPre _ hpc3,
      hs3]
  · rw [hb6.logs, hc.logs, hb13.logs, afterSstore_logs, afterSload_logs, afterSload_logs]
  · rw [hb6.output, hc.outputKeep, hb13.output, afterSstore_output, afterSload_output,
      afterSload_output]
  · rw [hb6.code, hc.code _ hpc3, hcode3]
  · exact WordAt.write_self _ _ _
  · exact WordAt.write_other (hw4 _ _ hL3.supply (by omega) (by omega) (by omega))
      (by simp only [B256.length_toBytes]; omega)
  · intro j hj
    exact WordAt.write_other (hw4 _ _ (hL3.amt j hj) (by omega) (by omega) (by omega))
      (by simp only [B256.length_toBytes]; omega)

end Blanc.Lift.Curve3Pool
