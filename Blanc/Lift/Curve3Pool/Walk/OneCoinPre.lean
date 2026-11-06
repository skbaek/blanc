import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXFirst
import Blanc.Lift.Curve3Pool.Walk.Exchange
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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

-- SEGMENT: ocA2
/-- **The guards and the quote, with the second `get_y_D` call** (`0x440c` → `0x4491`). -/
theorem xa_oc_a2 (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
      (IdReadyH sevm b → c.post.getCode 4 = c.pre.getCode 4 → IdReadyH sevm b') ∧
      XAt sevm post 0x4491 (St b' [dy, fee, Bytes.toB256 [0x00], Bytes.toB256 [0x00]] M' G') L' ∧
      VW M' [] ∧
      CwFirstGetYD s sevm.benvStat.time.toNat (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat
        ⟨(Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat, hi⟩ (vSupply c).toNat ∧
      CwSecondGetYD s sevm.benvStat.time.toNat (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat
        ⟨(Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat, hi⟩ (vSupply c).toNat := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x4410 (.push [0xff, 0xff, 0xff] (by decide)) ri_push  -- 440c PUSH3 0xffffff
  xw 0x4411 (.reg .sload) ri_sloadF  -- 4410 SLOAD
  xa 2
  xji 0x4416 0x441a hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xa 3
  xw 0x4422 (.reg .sstore) ri_sstoreF  -- 4421 SSTORE
  xa 3
  xji 0x4428 0x442c hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xlu 0x4430  -- 442f MLOAD
  xa 4
  xlu 0x4437  -- 4436 MLOAD
  xa 4
  xji 0x443e 0x4442 hw
  · xdead
  clear hw
  xa 7
  xji 0x444c 0x4450 hw
  · xdead
  clear hw
  xa 3
  xw 0x4455 (.reg .sload) ri_sloadF  -- 4454 SLOAD
  xa 2
  xji 0x445a 0x445e hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [isKilledSlot_lit, getStorVal_afterSstoreH_ne (by decide), getStorVal_afterSloadH,
      getStorVal_eq] at e
    exact e
  clear hw
  xa 3
  xsw 0x4465 0x140  -- 4464 MSTORE
  xa 2
  xsw 0x446b 0x160  -- 446a MSTORE
  xs 0x446e (.push [0x01, 0x40] (by decide)) ri_push  -- 446b PUSH2 0x0140
  xl 0x446f 0x140  -- 446e MLOAD
  xs 0x4472 (.push [0x01, 0x60] (by decide)) ri_push  -- 446f PUSH2 0x0160
  xl 0x4473 0x160  -- 4472 MLOAD
  xa 3
  xsw 0x447a 0x1a0  -- 4479 MSTORE
  xa 3
  xsw 0x4481 0x1c0  -- 4480 MSTORE
  xs 0x4484 (.push [0x01, 0xc0] (by decide)) ri_push  -- 4481 PUSH2 0x01c0
  xl 0x4485 0x1c0  -- 4484 MLOAD
  xs 0x4488 (.push [0x01, 0xa0] (by decide)) ri_push  -- 4485 PUSH2 0x01a0
  xl 0x4489 0x1a0  -- 4488 MLOAD
  xs 0x448b (.push [0x06] (by decide)) ri_push  -- 4489 PUSH1 0x06
  cvpc 0x448c  -- 448b PC
  xa 2
  xjmp 0x3cca  -- 4490 JUMP
  have hs2 : ∀ x, ((afterSloadH sevm (afterSstoreH sevm (afterSloadH sevm b
      (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
      (Bytes.toB256 [15])).getStor sevm.currentTarget).get x =
      ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [afterSloadH_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, lockSlot_lit,
      show Bytes.toB256 [1] = (1 : B256) from by decide]
  have ha2 := ha.of_lock fun x hx => by rw [hs2, Stor.get_set_ne _ (Ne.symm hx)]
  have htok2 := htok
  rw [← Stor.get_set_ne _ lock_ne_token (v := 1), ← hs2] at htok2
  obtain ⟨c, L', hi, dy, fee, b', M', G', hL, hsw, hmod, hfirst, hsec, hst, hlg, h, hV', hout, hcd, hid⟩ :=
    xa_cw2 hc hcode hfork ha2 (hV.sub (List.nil_subset _)) htok2 h
  obtain ⟨A, x0, x1, x2, D0, D1, y, -, -, -, -, -, hA, hxp, hD0, hD1, -, hy⟩ := hfirst
  rw [hs2, Stor.get_set_ne _ lock_ne_token] at hsw
  rw [show (Nat.toB256 17547 + Bytes.toB256 [6]).toNat = 0x4491 from by decide] at h
  refine ⟨hlock, hval, hkill, c, L', hi, dy, fee, b', M', G', hL, hsw, hmod,
    fun x => by rw [hst, hs2], by rw [hlg, afterSloadH_logs, afterSstoreH_logs, afterSloadH_logs],
    by rw [hout, afterSloadH_output, afterSstoreH_output, afterSloadH_output], fun x hx => ?_,
    fun hb h4 => hid (((hb.afterSloadH _).afterSstoreH _ _).afterSloadH _) h4, h, hV',
    ⟨A, x0, x1, x2, D0, D1, y, hA, hxp, hD0, hD1, hy⟩, hsec⟩
  rw [hcd x (by rw [afterSloadH_getCode, afterSstoreH_getCode, afterSloadH_getCode]; exact hx),
    afterSloadH_getCode, afterSstoreH_getCode, afterSloadH_getCode]

-- SEGMENT: ocA
/-- **The guards and the quote** (`0x440c` → `0x4491`). -/
theorem xa_oc_a (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
      (IdReadyH sevm b → c.post.getCode 4 = c.pre.getCode 4 → IdReadyH sevm b') ∧
      XAt sevm post 0x4491 (St b' [dy, fee, Bytes.toB256 [0x00], Bytes.toB256 [0x00]] M' G') L' ∧
      VW M' [] ∧
      CwFirstGetYD s sevm.benvStat.time.toNat (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat
        ⟨(Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat, hi⟩ (vSupply c).toNat := by
  obtain ⟨hlock, hval, hkill, c, L', hi, dy, fee, b', M', G', hL, hsw, hmod, hst, hlg, hout, hcd, hid, h, hV, hfirst, -⟩ :=
    xa_oc_a2 hc hcode hfork ha htok h
  exact ⟨hlock, hval, hkill, c, L', hi, dy, fee, b', M', G', hL, hsw, hmod, hst, hlg, hout, hcd, hid, h, hV, hfirst⟩

/-- `FEE_DENOMINATOR` as the runtime pushes it. -/
abbrev ocDen : B256 := Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]

/-- `self.balances[i] -= dy + dy_fee * admin_fee / FEE_DENOMINATOR`'s guard and store
(`0x4491` → `0x458e`). -/
theorem xa_oc_b (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
  xa 2
  xsw 0x4496 0x220  -- 4495 MSTORE
  xs 0x4499 (.push [0x02, 0x40] (by decide)) ri_push  -- 4496 PUSH2 0x0240
  xsw 0x449a 0x240  -- 4499 MSTORE
  xs 0x449d (.push [0x01, 0x60] (by decide)) ri_push  -- 449a PUSH2 0x0160
  xsw 0x449e 0x160  -- 449d MSTORE
  xs 0x44a1 (.push [0x01, 0x40] (by decide)) ri_push  -- 449e PUSH2 0x0140
  xsw 0x44a2 0x140  -- 44a1 MSTORE
  xa 2
  xl 0x44a7 0x220  -- 44a6 MLOAD
  xs 0x44aa (.push [0x01, 0x40] (by decide)) ri_push  -- 44a7 PUSH2 0x0140
  xsw 0x44ab 0x140  -- 44aa MSTORE
  xa 3
  xl 0x44b0 0x240  -- 44af MLOAD
  xs 0x44b3 (.push [0x01, 0x60] (by decide)) ri_push  -- 44b0 PUSH2 0x0160
  xsw 0x44b4 0x160  -- 44b3 MSTORE
  xa 3
  xsw 0x44be 0x260  -- 44bd MSTORE
  xa 2
  xsw 0x44c4 0x280  -- 44c3 MSTORE
  xa 2
  xsw 0x44ca 0x2a0  -- 44c9 MSTORE
  xa 2
  xsw 0x44ef 0x2c0  -- 44ee MSTORE
  xa 5
  xl 0x44fa 0x140  -- 44f9 MLOAD
  xa 3
  xji 0x4500 0x4506 hw
  · xs 0x4502 (.push [0x64] (by decide)) ri_push
    xs 0x4505 (.push [0x02, 0x7c] (by decide)) ri_push
    xrevert
  have hmin := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 7
  xji 0x4512 0x4516 hw
  · xdead
  clear hw
  xa 3
  xsw 0x451c 0xc0  -- 451b MSTORE
  xa 2
  xk 0x4521 0xc0  -- 4520 SHA3
  rw [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq] at h
  xa 2
  xw 0x4524 (.reg .sload) ri_sloadF  -- 4523 SLOAD
  xs 0x4527 (.push [0x01, 0x40] (by decide)) ri_push  -- 4524 PUSH2 0x0140
  xl 0x4528 0x140  -- 4527 MLOAD
  xs 0x452b (.push [0x01, 0x60] (by decide)) ri_push  -- 4528 PUSH2 0x0160
  xl 0x452c 0x160  -- 452b MLOAD
  xs 0x452e (.push [0x03] (by decide)) ri_push  -- 452c PUSH1 0x03
  xw 0x452f (.reg .sload) ri_sloadF  -- 452e SLOAD
  xa 12
  xji 0x453e 0x4542 hw
  · xdead
  have hmf := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x4556 0x455a hw
  · xdead
  clear hw
  xa 14
  xji 0x456b 0x456f hw
  · xdead
  have hadd := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 13
  xji 0x457f 0x4583 hw
  · xdead
  have hsub := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xw 0x458d (.reg .sstore) ri_sstoreF  -- 458c SSTORE
  xs 0x458e (.reg .pop) ri_pop  -- 458d POP
  have haf : (afterSloadH sevm b (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))).getStorVal
      sevm.currentTarget (Bytes.toB256 [3]) = σ.get adminFeeSlot := by
    rw [afterSloadH_getStorVal, getStorVal_eq, hB.stor, adminFeeSlot_lit]
  have hbal : b.getStorVal sevm.currentTarget (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) =
      σ.get (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) := by
    rw [getStorVal_eq, hB.stor]
  rw [haf] at hmf hadd hsub h
  rw [hbal] at hsub h
  refine ⟨hmin, hmf, hadd, hsub, _, _, _, ⟨fun x => ?_, ?_, ?_, ?_⟩, ?_, h, hV.sub ?_⟩
  · rw [afterSstoreH_getStor_self, Stor.get_set_ite, Stor.get_set_ite, afterSloadH_getStor,
      afterSloadH_getStor, hB.stor]
  · rw [afterSstoreH_getCode, afterSloadH_getCode, afterSloadH_getCode, hB.code]
  · rw [afterSstoreH_output, afterSloadH_output, afterSloadH_output, hB.output]
  · exact ((hB.id.afterSloadH _).afterSloadH _).afterSstoreH _ _
  · rw [afterSstoreH_logs, afterSloadH_logs, afterSloadH_logs]
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]


end

end Blanc.Lift.Curve3Pool
