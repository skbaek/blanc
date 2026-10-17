import Blanc.Lift.Curve3Pool.Walk.ExchangeFrame
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidity

/-!
# `exchange`, part 1: the guards, `rates`, `old_balances`, and the call of `_xp_mem`

From the arm's body (`0x2319`) to `_xp_mem`'s entry (`0x3a1`): `assert lock == 0; lock = 1`,
the non-payable guard, the `int128` clamps of `i` and `j`, `assert not self.is_killed`,
`rates` at `0x140`, `old_balances` at `0x1a0`, the nine frame words `0x140 … 0x240` pushed,
`old_balances` copied to `0x280`, and the call of `_xp_mem(old_balances)` with return tag
`0x2458`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- `RATES[0]` (`10^18`) and `RATES[1] = RATES[2]` (`10^30`) as the runtime pushes them. -/
abbrev exR0 : B256 := Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00]
abbrev exR1 : B256 :=
  Bytes.toB256 [0x0c, 0x9f, 0x2c, 0x9c, 0xd0, 0x46, 0x74, 0xed, 0xea, 0x40, 0x00, 0x00, 0x00]

theorem keccak_one_add (img : Bytes) (k : B256) :
    Bytes.keccak ((Bytes.writeAt img 0xc0 (Bytes.toB256 [1]).toBytes).sliceD 0xc0 0x20 0) + k =
      balancesBase + k := by
  rw [keccak_one]

theorem ex_bal0 : balancesBase = balancesBase + Nat.toB256 0 := by decide
theorem ex_bal1 : balancesBase + Bytes.toB256 [1] = balancesBase + Nat.toB256 1 := by decide
theorem ex_bal2 : balancesBase + Bytes.toB256 [2] = balancesBase + Nat.toB256 2 := by decide

/-- **`exchange` up to `_xp_mem`** (see the module note). -/
theorem xa_ex_pre {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x2319 (St b [] M G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧
    ∃ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (G1 : Nat) (z0 z1 z2 : B256),
      (∀ x, (b1.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) ∧
      b1.logs = b.logs ∧ b1.output = b.output ∧ (∀ a, b1.getCode a = b.getCode a) ∧
      (IdReady sevm b → IdReady sevm b1) ∧ Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      XAt sevm post 0x3a1 (St b1 [Nat.toB256 0x2458, balAt (b.getStor sevm.currentTarget) 0,
        balAt (b.getStor sevm.currentTarget) 1, balAt (b.getStor sevm.currentTarget) 2, z2, z1, z0,
        balAt (b.getStor sevm.currentTarget) 2, balAt (b.getStor sevm.currentTarget) 1,
        balAt (b.getStor sevm.currentTarget) 0, exR1, exR1, exR0, Bytes.toB256 [2, 0]] M1 G1) L := by
  xs 0x231d (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x231e (.reg .sload) ri_sload
  xs 0x231f (.reg .iszero) ri_iszero
  xs 0x2322 (.push [0x23, 0x27] (by decide)) ri_push
  xji 0x2323 0x2327 hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xjd 0x2328
  xs 0x232a (.push [0x01] (by decide)) ri_push
  xs 0x232e (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x232f (.reg .sstore) ri_sstore
  xs 0x2330 (.reg .callvalue) ri_callvalue
  xs 0x2331 (.reg .iszero) ri_iszero
  xs 0x2334 (.push [0x23, 0x39] (by decide)) ri_push
  xji 0x2335 0x2339 hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  refine ⟨hlock, hval, ?_⟩
  -- the clamps of `i` and `j`
  xjd 0x233a
  xs 0x233c (.push [0x60] (by decide)) ri_push
  xmo 0x233d (.reg .mload) (ri_mload_imgAt (o := 0x60) rfl)
  xs 0x233f (.push [0x04] (by decide)) ri_push
  xs 0x2340 (.reg .calldataload) ri_calldataload
  xs 0x2341 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2343 (.push [0x40] (by decide)) ri_push
  xmo 0x2344 (.reg .mload) (ri_mload_imgAt (o := 0x40) rfl)
  xs 0x2345 (.reg (.swap 0)) (ri_swap (by rfl))
  xs2 0x2346 (.reg .sgt) ri_sgt
  xs 0x2347 (.reg .iszero) ri_iszero
  xs 0x234a (.push [0x23, 0x4f] (by decide)) ri_push
  xji 0x234b 0x234f hw
  · xdead
  clear hw
  xjd 0x2350
  xs 0x2351 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2352 (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x2353 (.reg (.swap 0)) (ri_swap (by rfl))
  xs2 0x2354 (.reg .slt) ri_slt
  xs 0x2355 (.reg .iszero) ri_iszero
  xs 0x2358 (.push [0x23, 0x5d] (by decide)) ri_push
  xji 0x2359 0x235d hw
  · xdead
  clear hw
  xjd 0x235e
  xs 0x235f (.reg .pop) ri_pop
  xs 0x2361 (.push [0x60] (by decide)) ri_push
  xmo 0x2362 (.reg .mload) (ri_mload_imgAt (o := 0x60) rfl)
  xs 0x2364 (.push [0x24] (by decide)) ri_push
  xs 0x2365 (.reg .calldataload) ri_calldataload
  xs 0x2366 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2368 (.push [0x40] (by decide)) ri_push
  xmo 0x2369 (.reg .mload) (ri_mload_imgAt (o := 0x40) rfl)
  xs 0x236a (.reg (.swap 0)) (ri_swap (by rfl))
  xs2 0x236b (.reg .sgt) ri_sgt
  xs 0x236c (.reg .iszero) ri_iszero
  xs 0x236f (.push [0x23, 0x74] (by decide)) ri_push
  xji 0x2370 0x2374 hw
  · xdead
  clear hw
  xjd 0x2375
  xs 0x2376 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2377 (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x2378 (.reg (.swap 0)) (ri_swap (by rfl))
  xs2 0x2379 (.reg .slt) ri_slt
  xs 0x237a (.reg .iszero) ri_iszero
  xs 0x237d (.push [0x23, 0x82] (by decide)) ri_push
  xji 0x237e 0x2382 hw
  · xdead
  clear hw
  xjd 0x2383
  xs 0x2384 (.reg .pop) ri_pop
  -- `assert not self.is_killed`
  xs 0x2386 (.push [0x0f] (by decide)) ri_push
  xw 0x2387 (.reg .sload) ri_sload
  xs 0x2388 (.reg .iszero) ri_iszero
  xs 0x238b (.push [0x23, 0x90] (by decide)) ri_push
  xji 0x238c 0x2390 hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [isKilledSlot_lit, getStorVal_afterSstore_ne (by decide), getStorVal_afterSload,
      getStorVal_eq] at e
    exact e
  clear hw
  refine ⟨hkill, ?_⟩
  -- `rates`
  xjd 0x2391
  xs 0x2394 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x239d (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push
  xs 0x239e (.reg (.dup 1)) (ri_dup (by rfl))
  xmo 0x239f (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  xs 0x23ad (.push [0x0c, 0x9f, 0x2c, 0x9c, 0xd0, 0x46, 0x74, 0xed, 0xea, 0x40, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x23ae (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x23b0 (.push [0x20] (by decide)) ri_push
  xs 0x23b1 (.reg .add) ri_add
  xmo 0x23b2 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) (by decide))
  xs 0x23c0 (.push [0x0c, 0x9f, 0x2c, 0x9c, 0xd0, 0x46, 0x74, 0xed, 0xea, 0x40, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x23c1 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x23c3 (.push [0x40] (by decide)) ri_push
  xs 0x23c4 (.reg .add) ri_add
  xmo 0x23c5 (.reg .mstore) (ri_mstore_imgAt (o := 0x180) (by decide))
  xs 0x23c6 (.reg .pop) ri_pop
  -- `old_balances`
  xs 0x23c9 (.push [0x01, 0xa0] (by decide)) ri_push
  xs 0x23cb (.push [0x01] (by decide)) ri_push
  xs 0x23cc (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x23ce (.push [0xc0] (by decide)) ri_push
  xmo 0x23cf (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x23d1 (.push [0x20] (by decide)) ri_push
  xs 0x23d3 (.push [0xc0] (by decide)) ri_push
  xmo 0x23d4 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xw 0x23d5 (.reg .sload) ri_sload
  xs 0x23d6 (.reg (.dup 2)) (ri_dup (by rfl))
  xmo 0x23d7 (.reg .mstore) (ri_mstore_imgAt (o := 0x1a0) rfl)
  xs 0x23d9 (.push [0x01] (by decide)) ri_push
  xs 0x23da (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x23dc (.push [0xc0] (by decide)) ri_push
  xmo 0x23dd (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x23df (.push [0x20] (by decide)) ri_push
  xs 0x23e1 (.push [0xc0] (by decide)) ri_push
  xmo 0x23e2 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x23e3 (.reg .add) ri_add
  xw 0x23e4 (.reg .sload) ri_sload
  xs 0x23e5 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x23e7 (.push [0x20] (by decide)) ri_push
  xs 0x23e8 (.reg .add) ri_add
  xmo 0x23e9 (.reg .mstore) (ri_mstore_imgAt (o := 0x1c0) (by decide))
  xs 0x23eb (.push [0x02] (by decide)) ri_push
  xs 0x23ec (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x23ee (.push [0xc0] (by decide)) ri_push
  xmo 0x23ef (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x23f1 (.push [0x20] (by decide)) ri_push
  xs 0x23f3 (.push [0xc0] (by decide)) ri_push
  xmo 0x23f4 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x23f5 (.reg .add) ri_add
  xw 0x23f6 (.reg .sload) ri_sload
  xs 0x23f7 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x23f9 (.push [0x40] (by decide)) ri_push
  xs 0x23fa (.reg .add) ri_add
  xmo 0x23fb (.reg .mstore) (ri_mstore_imgAt (o := 0x1e0) (by decide))
  xs 0x23fc (.reg .pop) ri_pop
  xs 0x23fd (.reg .pop) ri_pop
  simp only [getStorVal_afterSload] at h hR
  rw [getStorVal_afterSstore_ne (by decide), getStorVal_afterSload, getStorVal_eq,
    getStorVal_afterSstore_ne (by decide), getStorVal_afterSload, getStorVal_eq,
    getStorVal_afterSstore_ne (by decide), getStorVal_afterSload, getStorVal_eq] at hR
  -- the frame words and the call of `_xp_mem`
  xs 0x2400 (.push [0x02, 0x00] (by decide)) ri_push
  xs 0x2403 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x2404 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  xs 0x2407 (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x2408 (.reg .mload) (ri_mload_imgAt (o := 0x160) rfl)
  xs 0x240b (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0x240c (.reg .mload) (ri_mload_imgAt (o := 0x180) rfl)
  xs 0x240f (.push [0x01, 0xa0] (by decide)) ri_push
  xmo 0x2410 (.reg .mload) (ri_mload_imgAt (o := 0x1a0) rfl)
  xs 0x2413 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0x2414 (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  xs 0x2417 (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x2418 (.reg .mload) (ri_mload_imgAt (o := 0x1e0) rfl)
  xs 0x241b (.push [0x02, 0x00] (by decide)) ri_push
  xmo 0x241c (.reg .mload) (ri_mload_imgAt (o := 0x200) rfl)
  xs 0x241f (.push [0x02, 0x20] (by decide)) ri_push
  xmo 0x2420 (.reg .mload) (ri_mload_imgAt (o := 0x220) rfl)
  xs 0x2423 (.push [0x02, 0x40] (by decide)) ri_push
  xmo 0x2424 (.reg .mload) (ri_mload_imgAt (o := 0x240) rfl)
  xs 0x2427 (.push [0x02, 0x80] (by decide)) ri_push
  xs 0x242a (.push [0x01, 0xa0] (by decide)) ri_push
  xs 0x242b (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x242c (.reg .mload) (ri_mload_imgAt (o := 0x1a0) rfl)
  xs 0x242d (.reg (.dup 2)) (ri_dup (by rfl))
  xmo 0x242e (.reg .mstore) (ri_mstore_imgAt (o := 0x280) rfl)
  xs 0x242f (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2431 (.push [0x20] (by decide)) ri_push
  xs 0x2432 (.reg .add) ri_add
  xmo 0x2433 (.reg .mload) (ri_mload_imgAt (o := 0x1c0) (by decide))
  xs 0x2434 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2436 (.push [0x20] (by decide)) ri_push
  xs 0x2437 (.reg .add) ri_add
  xmo 0x2438 (.reg .mstore) (ri_mstore_imgAt (o := 0x2a0) (by decide))
  xs 0x2439 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x243b (.push [0x40] (by decide)) ri_push
  xs 0x243c (.reg .add) ri_add
  xmo 0x243d (.reg .mload) (ri_mload_imgAt (o := 0x1e0) (by decide))
  xs 0x243e (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2440 (.push [0x40] (by decide)) ri_push
  xs 0x2441 (.reg .add) ri_add
  xmo 0x2442 (.reg .mstore) (ri_mstore_imgAt (o := 0x2c0) (by decide))
  xs 0x2443 (.reg .pop) ri_pop
  xs 0x2444 (.reg .pop) ri_pop
  xs 0x2447 (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x2448 (.reg .mload) (ri_mload_imgAt (o := 0x2c0) rfl)
  xs 0x244b (.push [0x02, 0xa0] (by decide)) ri_push
  xmo 0x244c (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  xs 0x244f (.push [0x02, 0x80] (by decide)) ri_push
  xmo 0x2450 (.reg .mload) (ri_mload_imgAt (o := 0x280) rfl)
  xs 0x2452 (.push [0x06] (by decide)) ri_push
  xpc 0x2453
  xs 0x2454 (.reg .add) ri_add
  xs 0x2457 (.push [0x03, 0xa1] (by decide)) ri_push
  xjmp 0x3a1
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
    at h
  obtain ⟨img1, hR1, -⟩ := Mem.Reads.forget hR
  have e0 : (b.getStor sevm.currentTarget).get balancesBase = balAt (b.getStor sevm.currentTarget) 0 := by
    show _ = (b.getStor _).get (balancesBase + Nat.toB256 0); rw [← ex_bal0]
  rw [ex_bal1, ex_bal2, e0, show Nat.toB256 9298 + Bytes.toB256 [6] = Nat.toB256 0x2458 by decide]
    at h
  refine ⟨_, _, img1, _, _, _, _, fun x => ?_, ?_, ?_, fun a => ?_, fun hid => ?_, hR1, hW, h⟩
  · simp only [afterSload_getStor, afterSstore_getStor_self, lockSlot_lit]
    rfl
  · simp only [afterSload_logs, afterSstore_logs]
  · simp only [afterSload_output, afterSstore_output]
  · simp only [afterSload_getCode, afterSstore_getCode]
  · exact (((((hid.afterSload _).afterSstore _ _).afterSload _).afterSload _).afterSload _).afterSload _

end Blanc.Lift.Curve3Pool
