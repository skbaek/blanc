import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXSpec
import Blanc.Lift.Curve3Pool.Walk.Exchange

/-!
# `remove_liquidity_one_coin`, part 1: the guards and `_calc_withdraw_one_coin`

* `xa_oc_a` (`0x440c` → `0x4491`): the lock (clear, then set), the non-payable guard, the
  `int128` clamp of `i`, `assert not self.is_killed`, the arguments stored and the child-aware
  `_calc_withdraw_one_coin` walk (`xa_cw`), which consumes the `totalSupply()` child.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: ocA
/-- **The guards and the quote** (`0x440c` → `0x4491`). -/
theorem xa_oc_a (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x440c (St b [] (vdMem sevm) G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧
    ∃ (c : Exec.Frame) (L' : List Exec.Frame)
      (hi : (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat < 3) (dy fee : B256) (b' : Devm)
      (M' : Mem) (G' : Nat), L = c :: L' ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      (∀ e : Env, e.time = sevm.benvStat.time.toNat → e.supply = some (vSupply c).toNat →
        calcWithdrawOne s e (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat
          ⟨(Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat, hi⟩ = some (dy.toNat, fee.toNat)) ∧
      (∀ x, (b'.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) ∧
      b'.logs = b.logs ∧ b'.output = b.output ∧
      (∀ x, b.getCode x ≠ .empty → b'.getCode x = b.getCode x) ∧
      (IdReady sevm b → c.post.getCode 4 = c.pre.getCode 4 → IdReady sevm b') ∧
      XAt sevm post 0x4491 (St b' [dy, fee, Bytes.toB256 [0x00], Bytes.toB256 [0x00]] M' G') L' ∧
      VW M' [] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x4410 (.push [0xff, 0xff, 0xff] (by decide)) ri_push  -- 440c PUSH3 0xffffff
  xw 0x4411 (.reg .sload) ri_sload  -- 4410 SLOAD
  xs 0x4412 (.reg .iszero) ri_iszero  -- 4411 ISZERO
  xs 0x4415 (.push [0x44, 0x1a] (by decide)) ri_push  -- 4412 PUSH2 0x441a
  xji 0x4416 0x441a hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xjd 0x441b  -- 441a JUMPDEST
  xs 0x441d (.push [0x01] (by decide)) ri_push  -- 441b PUSH1 0x01
  xs 0x4421 (.push [0xff, 0xff, 0xff] (by decide)) ri_push  -- 441d PUSH3 0xffffff
  xw 0x4422 (.reg .sstore) ri_sstore  -- 4421 SSTORE
  xs 0x4423 (.reg .callvalue) ri_callvalue  -- 4422 CALLVALUE
  xs 0x4424 (.reg .iszero) ri_iszero  -- 4423 ISZERO
  xs 0x4427 (.push [0x44, 0x2c] (by decide)) ri_push  -- 4424 PUSH2 0x442c
  xji 0x4428 0x442c hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x442d  -- 442c JUMPDEST
  xs 0x442f (.push [0x60] (by decide)) ri_push  -- 442d PUSH1 0x60
  xlu 0x4430  -- 442f MLOAD
  xs 0x4432 (.push [0x24] (by decide)) ri_push  -- 4430 PUSH1 0x24
  xs 0x4433 (.reg .calldataload) ri_calldataload  -- 4432 CALLDATALOAD
  xs 0x4434 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4433 DUP1
  xs 0x4436 (.push [0x40] (by decide)) ri_push  -- 4434 PUSH1 0x40
  xlu 0x4437  -- 4436 MLOAD
  xs 0x4438 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4437 SWAP1
  xs2 0x4439 (.reg .sgt) ri_sgt  -- 4438 SGT
  xs 0x443a (.reg .iszero) ri_iszero  -- 4439 ISZERO
  xs 0x443d (.push [0x44, 0x42] (by decide)) ri_push  -- 443a PUSH2 0x4442
  xji 0x443e 0x4442 hw
  · xdead
  clear hw
  xjd 0x4443  -- 4442 JUMPDEST
  xs 0x4444 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4443 DUP1
  xs 0x4445 (.reg (.swap 1)) (ri_swap (by rfl))  -- 4444 SWAP2
  xs 0x4446 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4445 SWAP1
  xs2 0x4447 (.reg .slt) ri_slt  -- 4446 SLT
  xs 0x4448 (.reg .iszero) ri_iszero  -- 4447 ISZERO
  xs 0x444b (.push [0x44, 0x50] (by decide)) ri_push  -- 4448 PUSH2 0x4450
  xji 0x444c 0x4450 hw
  · xdead
  clear hw
  xjd 0x4451  -- 4450 JUMPDEST
  xs 0x4452 (.reg .pop) ri_pop  -- 4451 POP
  xs 0x4454 (.push [0x0f] (by decide)) ri_push  -- 4452 PUSH1 0x0f
  xw 0x4455 (.reg .sload) ri_sload  -- 4454 SLOAD
  xs 0x4456 (.reg .iszero) ri_iszero  -- 4455 ISZERO
  xs 0x4459 (.push [0x44, 0x5e] (by decide)) ri_push  -- 4456 PUSH2 0x445e
  xji 0x445a 0x445e hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [isKilledSlot_lit, getStorVal_afterSstore_ne (by decide), getStorVal_afterSload,
      getStorVal_eq] at e
    exact e
  clear hw
  xjd 0x445f  -- 445e JUMPDEST
  xs 0x4461 (.push [0x00] (by decide)) ri_push  -- 445f PUSH1 0x00
  xs 0x4464 (.push [0x01, 0x40] (by decide)) ri_push  -- 4461 PUSH2 0x0140
  xsw 0x4465 0x140  -- 4464 MSTORE
  xs 0x4467 (.push [0x00] (by decide)) ri_push  -- 4465 PUSH1 0x00
  xs 0x446a (.push [0x01, 0x60] (by decide)) ri_push  -- 4467 PUSH2 0x0160
  xsw 0x446b 0x160  -- 446a MSTORE
  xs 0x446e (.push [0x01, 0x40] (by decide)) ri_push  -- 446b PUSH2 0x0140
  xl 0x446f 0x140  -- 446e MLOAD
  xs 0x4472 (.push [0x01, 0x60] (by decide)) ri_push  -- 446f PUSH2 0x0160
  xl 0x4473 0x160  -- 4472 MLOAD
  xs 0x4475 (.push [0x04] (by decide)) ri_push  -- 4473 PUSH1 0x04
  xs 0x4476 (.reg .calldataload) ri_calldataload  -- 4475 CALLDATALOAD
  xs 0x4479 (.push [0x01, 0xa0] (by decide)) ri_push  -- 4476 PUSH2 0x01a0
  xsw 0x447a 0x1a0  -- 4479 MSTORE
  xs 0x447c (.push [0x24] (by decide)) ri_push  -- 447a PUSH1 0x24
  xs 0x447d (.reg .calldataload) ri_calldataload  -- 447c CALLDATALOAD
  xs 0x4480 (.push [0x01, 0xc0] (by decide)) ri_push  -- 447d PUSH2 0x01c0
  xsw 0x4481 0x1c0  -- 4480 MSTORE
  xs 0x4484 (.push [0x01, 0xc0] (by decide)) ri_push  -- 4481 PUSH2 0x01c0
  xl 0x4485 0x1c0  -- 4484 MLOAD
  xs 0x4488 (.push [0x01, 0xa0] (by decide)) ri_push  -- 4485 PUSH2 0x01a0
  xl 0x4489 0x1a0  -- 4488 MLOAD
  xs 0x448b (.push [0x06] (by decide)) ri_push  -- 4489 PUSH1 0x06
  cvpc 0x448c  -- 448b PC
  xs 0x448d (.reg .add) ri_add  -- 448c ADD
  xs 0x4490 (.push [0x3c, 0xca] (by decide)) ri_push  -- 448d PUSH2 0x3cca
  xjmp 0x3cca  -- 4490 JUMP
  have hs2 : ∀ x, ((afterSload sevm (afterSstore sevm (afterSload sevm b
      (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
      (Bytes.toB256 [15])).getStor sevm.currentTarget).get x =
      ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [afterSload_getStor, afterSstore_getStor_self, afterSload_getStor, lockSlot_lit,
      show Bytes.toB256 [1] = (1 : B256) from by decide]
  have ha2 := ha.of_lock fun x hx => by rw [hs2, Stor.get_set_ne _ (Ne.symm hx)]
  have htok2 := htok
  rw [← Stor.get_set_ne _ lock_ne_token (v := 1), ← hs2] at htok2
  obtain ⟨c, L', hi, dy, fee, b', M', G', hL, hsw, hmod, -, hst, hlg, h, hV', hout, hcd, hid⟩ :=
    xa_cw hc hcode hfork ha2 (hV.sub (List.nil_subset _)) htok2 h
  rw [hs2, Stor.get_set_ne _ lock_ne_token] at hsw
  rw [show (Nat.toB256 17547 + Bytes.toB256 [6]).toNat = 0x4491 from by decide] at h
  refine ⟨hlock, hval, hkill, c, L', hi, dy, fee, b', M', G', hL, hsw, hmod,
    fun x => by rw [hst, hs2], by rw [hlg, afterSload_logs, afterSstore_logs, afterSload_logs],
    by rw [hout, afterSload_output, afterSstore_output, afterSload_output], fun x hx => ?_,
    fun hb h4 => hid (((hb.afterSload _).afterSstore _ _).afterSload _) h4, h, hV'⟩
  rw [hcd x (by rw [afterSload_getCode, afterSstore_getCode, afterSload_getCode]; exact hx),
    afterSload_getCode, afterSstore_getCode, afterSload_getCode]

/-- `FEE_DENOMINATOR` as the runtime pushes it. -/
abbrev ocDen : B256 := Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]

/-- `self.balances[i] -= dy + dy_fee * admin_fee / FEE_DENOMINATOR`'s guard and store
(`0x4491` → `0x458e`). -/
theorem xa_oc_b (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {b0 : Devm} {σ : Stor} {M : Mem} {dy fee : B256} (hB : ExBase sevm b0 b σ) (hV : VW M [])
    (h : XAt sevm post 0x4491 (St b [dy, fee, Bytes.toB256 [0x00], Bytes.toB256 [0x00]] M G) L) :
    ¬ dy < Sevm.dataWord sevm (Bytes.toB256 [0x44]) ∧ fee.Nofm (σ.get adminFeeSlot) ∧
    ¬ dy + fee * σ.get adminFeeSlot / ocDen < dy ∧
    ¬ σ.get (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [0x24])) <
      dy + fee * σ.get adminFeeSlot / ocDen ∧
    ∃ (b' : Devm) (M' : Mem) (G' : Nat),
      ExBase sevm b0 b' (σ.set (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [0x24]))
        (σ.get (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [0x24])) -
          (dy + fee * σ.get adminFeeSlot / ocDen))) ∧ b'.logs = b.logs ∧
      XAt sevm post 0x458e (St b' [] M' G') L ∧ VW M' [(0x140, dy)] := by
  xjd 0x4492  -- 4491 JUMPDEST
  xs 0x4495 (.push [0x02, 0x20] (by decide)) ri_push  -- 4492 PUSH2 0x0220
  xsw 0x4496 0x220  -- 4495 MSTORE
  xs 0x4499 (.push [0x02, 0x40] (by decide)) ri_push  -- 4496 PUSH2 0x0240
  xsw 0x449a 0x240  -- 4499 MSTORE
  xs 0x449d (.push [0x01, 0x60] (by decide)) ri_push  -- 449a PUSH2 0x0160
  xsw 0x449e 0x160  -- 449d MSTORE
  xs 0x44a1 (.push [0x01, 0x40] (by decide)) ri_push  -- 449e PUSH2 0x0140
  xsw 0x44a2 0x140  -- 44a1 MSTORE
  xs 0x44a5 (.push [0x02, 0x20] (by decide)) ri_push  -- 44a2 PUSH2 0x0220
  xs 0x44a6 (.reg (.dup 0)) (ri_dup (by rfl))  -- 44a5 DUP1
  xl 0x44a7 0x220  -- 44a6 MLOAD
  xs 0x44aa (.push [0x01, 0x40] (by decide)) ri_push  -- 44a7 PUSH2 0x0140
  xsw 0x44ab 0x140  -- 44aa MSTORE
  xs 0x44ad (.push [0x20] (by decide)) ri_push  -- 44ab PUSH1 0x20
  xs 0x44ae (.reg (.dup 1)) (ri_dup (by rfl))  -- 44ad DUP2
  xs 0x44af (.reg .add) ri_add  -- 44ae ADD
  xl 0x44b0 0x240  -- 44af MLOAD
  xs 0x44b3 (.push [0x01, 0x60] (by decide)) ri_push  -- 44b0 PUSH2 0x0160
  xsw 0x44b4 0x160  -- 44b3 MSTORE
  xs 0x44b5 (.reg .pop) ri_pop  -- 44b4 POP
  xs 0x44ba (.push [0x08, 0xc3, 0x79, 0xa0] (by decide)) ri_push  -- 44b5 PUSH4 0x08c379a0
  xs 0x44bd (.push [0x02, 0x60] (by decide)) ri_push  -- 44ba PUSH2 0x0260
  xsw 0x44be 0x260  -- 44bd MSTORE
  xs 0x44c0 (.push [0x20] (by decide)) ri_push  -- 44be PUSH1 0x20
  xs 0x44c3 (.push [0x02, 0x80] (by decide)) ri_push  -- 44c0 PUSH2 0x0280
  xsw 0x44c4 0x280  -- 44c3 MSTORE
  xs 0x44c6 (.push [0x18] (by decide)) ri_push  -- 44c4 PUSH1 0x18
  xs 0x44c9 (.push [0x02, 0xa0] (by decide)) ri_push  -- 44c6 PUSH2 0x02a0
  xsw 0x44ca 0x2a0  -- 44c9 MSTORE
  xs 0x44eb (.push [0x4e, 0x6f, 0x74, 0x20, 0x65, 0x6e, 0x6f, 0x75, 0x67, 0x68, 0x20, 0x63, 0x6f, 0x69, 0x6e, 0x73, 0x20, 0x72, 0x65, 0x6d, 0x6f, 0x76, 0x65, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 44ca PUSH32 0x4e6f7420656e6f75676820636f696e732072656d6f7665640000000000000000
  xs 0x44ee (.push [0x02, 0xc0] (by decide)) ri_push  -- 44eb PUSH2 0x02c0
  xsw 0x44ef 0x2c0  -- 44ee MSTORE
  xs 0x44f2 (.push [0x02, 0xa0] (by decide)) ri_push  -- 44ef PUSH2 0x02a0
  xs 0x44f3 (.reg .pop) ri_pop  -- 44f2 POP
  xs 0x44f5 (.push [0x44] (by decide)) ri_push  -- 44f3 PUSH1 0x44
  xs 0x44f6 (.reg .calldataload) ri_calldataload  -- 44f5 CALLDATALOAD
  xs 0x44f9 (.push [0x01, 0x40] (by decide)) ri_push  -- 44f6 PUSH2 0x0140
  xl 0x44fa 0x140  -- 44f9 MLOAD
  xs 0x44fb (.reg .lt) ri_lt  -- 44fa LT
  xs 0x44fc (.reg .iszero) ri_iszero  -- 44fb ISZERO
  xs 0x44ff (.push [0x45, 0x06] (by decide)) ri_push  -- 44fc PUSH2 0x4506
  xji 0x4500 0x4506 hw
  · xs 0x4502 (.push [0x64] (by decide)) ri_push
    xs 0x4505 (.push [0x02, 0x7c] (by decide)) ri_push
    xrevert
  have hmin := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x4507  -- 4506 JUMPDEST
  xs 0x4509 (.push [0x24] (by decide)) ri_push  -- 4507 PUSH1 0x24
  xs 0x450a (.reg .calldataload) ri_calldataload  -- 4509 CALLDATALOAD
  xs 0x450c (.push [0x03] (by decide)) ri_push  -- 450a PUSH1 0x03
  xs 0x450d (.reg (.dup 1)) (ri_dup (by rfl))  -- 450c DUP2
  xs 0x450e (.reg .lt) ri_lt  -- 450d LT
  xs 0x4511 (.push [0x45, 0x16] (by decide)) ri_push  -- 450e PUSH2 0x4516
  xji 0x4512 0x4516 hw
  · xdead
  clear hw
  xjd 0x4517  -- 4516 JUMPDEST
  xs 0x4519 (.push [0x01] (by decide)) ri_push  -- 4517 PUSH1 0x01
  xs 0x451b (.push [0xc0] (by decide)) ri_push  -- 4519 PUSH1 0xc0
  xsw 0x451c 0xc0  -- 451b MSTORE
  xs 0x451e (.push [0x20] (by decide)) ri_push  -- 451c PUSH1 0x20
  xs 0x4520 (.push [0xc0] (by decide)) ri_push  -- 451e PUSH1 0xc0
  xk 0x4521 0xc0  -- 4520 SHA3
  rw [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq] at h
  xs 0x4522 (.reg .add) ri_add  -- 4521 ADD
  xs 0x4523 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4522 DUP1
  xw 0x4524 (.reg .sload) ri_sload  -- 4523 SLOAD
  xs 0x4527 (.push [0x01, 0x40] (by decide)) ri_push  -- 4524 PUSH2 0x0140
  xl 0x4528 0x140  -- 4527 MLOAD
  xs 0x452b (.push [0x01, 0x60] (by decide)) ri_push  -- 4528 PUSH2 0x0160
  xl 0x452c 0x160  -- 452b MLOAD
  xs 0x452e (.push [0x03] (by decide)) ri_push  -- 452c PUSH1 0x03
  xw 0x452f (.reg .sload) ri_sload  -- 452e SLOAD
  xs 0x4530 (.reg (.dup 0)) (ri_dup (by rfl))  -- 452f DUP1
  xs 0x4531 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4530 DUP3
  xs 0x4532 (.reg .mul) ri_mul  -- 4531 MUL
  xs 0x4533 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4532 DUP3
  xs 0x4534 (.reg .iszero) ri_iszero  -- 4533 ISZERO
  xs 0x4535 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4534 DUP3
  xs 0x4536 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4535 DUP5
  xs 0x4537 (.reg (.dup 3)) (ri_dup (by rfl))  -- 4536 DUP4
  xs 0x4538 (.reg .div) ri_div  -- 4537 DIV
  xs 0x4539 (.reg .eq) ri_eq  -- 4538 EQ
  xs 0x453a (.reg .or) ri_or  -- 4539 OR
  xs 0x453d (.push [0x45, 0x42] (by decide)) ri_push  -- 453a PUSH2 0x4542
  xji 0x453e 0x4542 hw
  · xdead
  have hmf := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x4543  -- 4542 JUMPDEST
  xs 0x4544 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4543 DUP1
  xs 0x4545 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4544 SWAP1
  xs 0x4546 (.reg .pop) ri_pop  -- 4545 POP
  xs 0x4547 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4546 SWAP1
  xs 0x4548 (.reg .pop) ri_pop  -- 4547 POP
  xs 0x4549 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4548 SWAP1
  xs 0x454a (.reg .pop) ri_pop  -- 4549 POP
  xs 0x4550 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 454a PUSH5 0x02540be400
  xs 0x4551 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4550 DUP1
  xs 0x4552 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4551 DUP1
  xs 0x4555 (.push [0x45, 0x5a] (by decide)) ri_push  -- 4552 PUSH2 0x455a
  xji 0x4556 0x455a hw
  · xdead
  clear hw
  xjd 0x455b  -- 455a JUMPDEST
  xs 0x455c (.reg (.dup 2)) (ri_dup (by rfl))  -- 455b DUP3
  xs 0x455d (.reg .div) ri_div  -- 455c DIV
  xs 0x455e (.reg (.swap 0)) (ri_swap (by rfl))  -- 455d SWAP1
  xs 0x455f (.reg .pop) ri_pop  -- 455e POP
  xs 0x4560 (.reg (.swap 0)) (ri_swap (by rfl))  -- 455f SWAP1
  xs 0x4561 (.reg .pop) ri_pop  -- 4560 POP
  xs 0x4562 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4561 DUP2
  xs 0x4563 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4562 DUP2
  xs 0x4564 (.reg (.dup 3)) (ri_dup (by rfl))  -- 4563 DUP4
  xs 0x4565 (.reg .add) ri_add  -- 4564 ADD
  xs 0x4566 (.reg .lt) ri_lt  -- 4565 LT
  xs 0x4567 (.reg .iszero) ri_iszero  -- 4566 ISZERO
  xs 0x456a (.push [0x45, 0x6f] (by decide)) ri_push  -- 4567 PUSH2 0x456f
  xji 0x456b 0x456f hw
  · xdead
  have hadd := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x4570  -- 456f JUMPDEST
  xs 0x4571 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4570 DUP1
  xs 0x4572 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4571 DUP3
  xs 0x4573 (.reg .add) ri_add  -- 4572 ADD
  xs 0x4574 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4573 SWAP1
  xs 0x4575 (.reg .pop) ri_pop  -- 4574 POP
  xs 0x4576 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4575 SWAP1
  xs 0x4577 (.reg .pop) ri_pop  -- 4576 POP
  xs 0x4578 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4577 DUP1
  xs 0x4579 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4578 DUP3
  xs 0x457a (.reg .lt) ri_lt  -- 4579 LT
  xs 0x457b (.reg .iszero) ri_iszero  -- 457a ISZERO
  xs 0x457e (.push [0x45, 0x83] (by decide)) ri_push  -- 457b PUSH2 0x4583
  xji 0x457f 0x4583 hw
  · xdead
  have hsub := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x4584  -- 4583 JUMPDEST
  xs 0x4585 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4584 DUP1
  xs 0x4586 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4585 DUP3
  xs 0x4587 (.reg .sub) ri_sub  -- 4586 SUB
  xs 0x4588 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4587 SWAP1
  xs 0x4589 (.reg .pop) ri_pop  -- 4588 POP
  xs 0x458a (.reg (.swap 0)) (ri_swap (by rfl))  -- 4589 SWAP1
  xs 0x458b (.reg .pop) ri_pop  -- 458a POP
  xs 0x458c (.reg (.dup 1)) (ri_dup (by rfl))  -- 458b DUP2
  xw 0x458d (.reg .sstore) ri_sstore  -- 458c SSTORE
  xs 0x458e (.reg .pop) ri_pop  -- 458d POP
  have haf : (afterSload sevm b (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))).getStorVal
      sevm.currentTarget (Bytes.toB256 [3]) = σ.get adminFeeSlot := by
    rw [afterSload_getStorVal, getStorVal_eq, hB.stor, adminFeeSlot_lit]
  have hbal : b.getStorVal sevm.currentTarget (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) =
      σ.get (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) := by
    rw [getStorVal_eq, hB.stor]
  rw [haf] at hmf hadd hsub h
  rw [hbal] at hsub h
  refine ⟨hmin, hmf, hadd, hsub, _, _, _, ⟨fun x => ?_, ?_, ?_, ?_⟩, ?_, h, hV.sub ?_⟩
  · rw [afterSstore_getStor_self, Stor.get_set_ite, Stor.get_set_ite, afterSload_getStor,
      afterSload_getStor, hB.stor]
  · rw [afterSstore_getCode, afterSload_getCode, afterSload_getCode, hB.code]
  · rw [afterSstore_output, afterSload_output, afterSload_output, hB.output]
  · exact ((hB.id.afterSload _).afterSload _).afterSstore _ _
  · rw [afterSstore_logs, afterSload_logs, afterSload_logs]
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
