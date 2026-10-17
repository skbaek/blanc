import Blanc.Lift.Curve3Pool.Walk.OneCoinCalls

/-!
# `remove_liquidity_one_coin`: the whole frame on the actual derivation

`xa_oneCoin` composes the dispatcher (`xa_vd_removeLiquidityOneCoin`), the guards and the
child-aware `_calc_withdraw_one_coin` walk (`xa_oc_a`), the slippage check and the balance
store (`xa_oc_b`), the `burnFrom` call (`xa_oc_burn`), the `transfer` push with its `raw_call`
test (`xa_oc_push`, `xa_oc_tail`) and the event with the lock clear (`xa_oc_log`): from the
frame's entry with the `remove_liquidity_one_coin` selector, a successful frame has exactly
three children (the static `totalSupply()`, the burn and the push), the machine-word checks the
model makes, and the pool's storage, logs and output as the model's step leaves them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

/-- **The dispatcher hands `removeLiquidityOneCoin` its body** (`0x440c`), with the
prologue's exact memory and the frame's remaining children unchanged. -/
theorem xa_vd_removeLiquidityOneCoin (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x440c (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_090e hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0af9 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0e47 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_189d hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_1d14 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2046 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_230b hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2c5a hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_3041 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_3992 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_3cc3 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_438a hcode h).miss (by rw [hsel]; decide)
  exact (xa_vd_arm_43fe hcode h).hit hsel

/-- `balances[i]`'s new word: `balances[i] - (dy + dy_fee * admin_fee / FEE_DENOMINATOR)`. -/
abbrev ocBal (σ : Stor) (iw dy fee : B256) : B256 :=
  σ.get (balancesBase + iw) - (dy + fee * σ.get adminFeeSlot / ocDen)

/-- **The `remove_liquidity_one_coin` frame.** From the frame's entry with the
`remove_liquidity_one_coin` selector over the entry storage `σ` (abstracting `s`), a successful
frame found the lock clear, no value and the pool alive; `i < 3`; its children are the static
`totalSupply()` reply `cs`, the `burnFrom` `cb` and the `transfer` `cp`; `_calc_withdraw_one_coin`
returned `(dy, dy_fee)` (`calcWithdrawOne` at the frame's time and the reply as supply); every
machine-word check of lines 679–681 passed; the pool's storage is `σ` with `balances[i]`
stored; the frame logged its children's logs and then `RemoveLiquidityOne`; the output is the
entry output. -/
theorem xa_oneCoin (hc : Cert.CheckedM code cert mems true) {σ : Stor} {s : State}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (hσ : b.getStor sevm.currentTarget = σ) (ha : Abstracts σ s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp (σ.get tokenSlot).toAdr)
    (hcoin : (exJ sevm).toNat < 3 →
      ¬ sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + exJ sevm)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    σ.get lockSlot = 0 ∧ sevm.value = 0 ∧ σ.get isKilledSlot = 0 ∧
    ∃ (cs cb cp : Exec.Frame) (hi : (exJ sevm).toNat < 3) (dy fee : B256),
      L = [cs, cb, cp] ∧
      StaticWordChild (σ.get tokenSlot).toAdr totalSupplyData cs ∧
      (∀ e : Env, e.time = sevm.benvStat.time.toNat → e.supply = some (vSupply cs).toNat →
        calcWithdrawOne s e (ocAmt sevm).toNat ⟨(exJ sevm).toNat, hi⟩ =
          some (dy.toNat, fee.toNat)) ∧
      ¬ dy < Sevm.dataWord sevm (Bytes.toB256 [0x44]) ∧ fee.Nofm (σ.get adminFeeSlot) ∧
      ¬ dy + fee * σ.get adminFeeSlot / ocDen < dy ∧
      ¬ σ.get (balancesBase + exJ sevm) < dy + fee * σ.get adminFeeSlot / ocDen ∧
      cb.sevm.currentTarget = (σ.get tokenSlot).toAdr ∧
      cb.sevm.data = burnFromSel ++ sevm.caller.toB256.toBytes ++ (ocAmt sevm).toBytes ∧
      cb.sevm.value = 0 ∧ cb.sevm.isStatic = sevm.isStatic ∧ 32 ≤ cb.post.output.length ∧
      cp.sevm.currentTarget = (σ.get (coinsBase + exJ sevm)).toAdr ∧
      cp.sevm.data = exPushData sevm dy ∧ cp.sevm.value = 0 ∧ cp.sevm.isStatic = sevm.isStatic ∧
      RawCallOk cp.post.output ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        (σ.set (balancesBase + exJ sevm) (ocBal σ (exJ sevm) dy fee)).get x) ∧
      post.logs = b.logs ++ [cs, cb, cp].flatMap (fun c => c.post.logs) ++
        [⟨sevm.currentTarget, [ocTopic, sevm.caller.toB256],
          (ocAmt sevm).toBytes ++ dy.toBytes⟩] ∧
      post.output = b.output := by
  subst hσ
  obtain ⟨_, h⟩ := xa_vd_removeLiquidityOneCoin hcode hlen hcd hsel h
  obtain ⟨hlock, hval, hkill, cs, L1, hi, dy, fee, b1, M1, G1, rfl, hsw, hmod, hs1, hl1, ho1,
    hc1, hid1, h, hV⟩ := xa_oc_a hc hcode hfork ha htok h
  refine ⟨hlock, hval, hkill, ?_⟩
  have hB1 : ExBase sevm b b1 ((b.getStor sevm.currentTarget).set lockSlot 1) :=
    ⟨hs1, hc1 _ hpc, ho1, hid1 hid (hidk cs List.mem_cons_self)⟩
  have hk1 : ∀ c ∈ L1, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x :=
    fun c hc => hkeep c (List.mem_cons_of_mem _ hc)
  have hi1 : ∀ c ∈ L1, c.post.getCode 4 = c.pre.getCode 4 :=
    fun c hc => hidk c (List.mem_cons_of_mem _ hc)
  clear hkeep hidk
  obtain ⟨hmin, hmf, hadd, hsub, b2, M2, G2, hB2, hl2, h, hV⟩ := xa_oc_b hcode hfork hB1 hV h
  have hiN : balancesBase + exJ sevm = balancesBase + Nat.toB256 (exJ sevm).toNat := by
    rw [toB256_toNat]
  have hcJ : coinsBase + exJ sevm = coinsBase + Nat.toB256 (exJ sevm).toNat := by
    rw [toB256_toNat]
  have htw : (b2.getStor sevm.currentTarget).get tokenSlot =
      (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [hB2.stor, Stor.get_set_ne _ (by rw [hiN]; exact bal_ne_token hi),
      Stor.get_set_ne _ lock_ne_token]
  have hadm : ((b.getStor sevm.currentTarget).set lockSlot 1).get adminFeeSlot =
      (b.getStor sevm.currentTarget).get adminFeeSlot :=
    Stor.get_set_ne _ (show lockSlot ≠ adminFeeSlot by decide) _
  have hbK : ((b.getStor sevm.currentTarget).set lockSlot 1).get (balancesBase + exJ sevm) =
      (b.getStor sevm.currentTarget).get (balancesBase + exJ sevm) :=
    Stor.get_set_ne _ (show lockSlot ≠ balancesBase + exJ sevm by rw [hiN]; exact bal_ne_lock hi) _
  rw [hadm] at hmf hadd hsub hB2
  rw [hbK] at hsub hB2
  -- the burn
  obtain ⟨cb, L2, d3, M3, img3, G3, rfl, hcb, hlen3, hdepth, hR3, hW3, hv3, h⟩ :=
    xa_oc_burn hcode hfork hV htw htok h
  have hB3 := hB2.child hcb hpc (hk1 cb List.mem_cons_self) (hi1 cb List.mem_cons_self)
  have hcw : (d3.getStor sevm.currentTarget).get (coinsBase + exJ sevm) =
      (b.getStor sevm.currentTarget).get (coinsBase + exJ sevm) := by
    rw [hB3.stor, Stor.get_set_ne _ (by rw [hiN, hcJ]; exact bal_ne_coin hi hi),
      Stor.get_set_ne _ (by rw [hcJ]; exact coin_ne_lock hi)]
  -- the push and its `raw_call` test
  obtain ⟨bq, cp, L3, dq, img9, G9, hbq, rfl, hcp, hv9, hR9, hW9, hrd9, h⟩ :=
    xa_oc_push hcode hfork hi hR3 hW3 hv3 hB3.id hdepth hcw (hcoin hi) h
  have hBq := (hB3.rel hbq).child hcp hpc (hk1 cp (by simp only [List.mem_cons, true_or, or_true]))
    (hi1 cp (by simp only [List.mem_cons, true_or, or_true]))
  obtain ⟨hok2, b10, M10, img10, G10, hb10, hR10, hW10, hk10, h⟩ :=
    xa_oc_tail hcode hBq.id hR9 hW9 hrd9 h
  -- the event and the lock
  obtain ⟨rfl, hsP, hlP, hoP⟩ := xa_oc_log hcode hfork hR10 hW10
    (hk10 _ _ hv9 (by omega) (by omega)) h
  refine ⟨cs, cb, cp, hi, dy, fee, rfl, hsw, hmod, hmin, hmf, hadd, hsub, hcb.target, hcb.data,
    hcb.value, hcb.isStatic, hlen3, hcp.target, hcp.data, hcp.value, hcp.isStatic,
    hcp.output ▸ hok2, fun x => ?_, ?_, ?_⟩
  · rw [hsP, Stor.get_set_ite, hb10.stor, hBq.stor]
    by_cases hx : lockSlot = x
    · subst hx
      rw [ite_eq_left rfl, Stor.get_set_ne _ (by rw [hiN]; exact (bal_ne_lock hi).symm), hlock]
    · rw [ite_eq_right hx, Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite, ite_eq_right hx]
  · rw [hlP, hb10.logs, hcp.logs, hbq.logs, hcb.logs, hl2, hl1]
    simp only [hsw.logs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
      List.append_assoc]
  · rw [hoP, hb10.output, hcp.outputKeep, hbq.output, hcb.outputKeep, hB2.output]

end

end Blanc.Lift.Curve3Pool
