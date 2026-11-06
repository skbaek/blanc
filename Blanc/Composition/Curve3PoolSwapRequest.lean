import Blanc.Composition.Curve3PoolExitMoment
import Blanc.Composition.Curve3PoolExitRequest
import Blanc.Composition.Curve3PoolPublicBridge
import Blanc.Lift.Curve3Pool.U3Ledger
import Blanc.Lift.Curve3Pool.ExchangeFloorFrame

/-!
# `SwapRequest` is what the model's `exchange` asks

`exchange_accepts`: the model accepts a swap the curve quotes, whose fee words are bounded, as every state of the
deployment's history has them (`Moment.feesWithin`), and whose admin cut fits. `swap_args`: `swapCalldata`'s decoded words.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 Env Out rates precision feeDen xpChk aChk pullIn)
open Blanc.StableSwapNewton (chkAdd chkMul chkDiv chkSub getYChk)

/-! ## The fees are bounded -/

/-- The four fee words within the constructor's and `commit_new_fee`'s limits. -/
def FeesBounded (s : Curve3Pool.State) : Prop :=
  s.fee ≤ Curve3Pool.maxFee ∧ s.futureFee ≤ Curve3Pool.maxFee ∧ s.adminFee ≤ Curve3Pool.maxAdminFee ∧
    s.futureAdminFee ≤ Curve3Pool.maxAdminFee

open Curve3Pool in
theorem body_feesBounded (s : Curve3Pool.State) (e : Env) (c : Call) (hs : FeesBounded s) :
    OptAll (fun o => FeesBounded o.state) (body s e c) := by
  cases c <;> simp only [body, Curve3Pool.addLiquidity, Curve3Pool.exchange,
    Curve3Pool.removeLiquidity, Curve3Pool.removeLiquidityImbalance,
    Curve3Pool.removeLiquidityOneCoin, Curve3Pool.rampA, Curve3Pool.stopRampA,
    Curve3Pool.commitNewFee, Curve3Pool.applyNewFee, Curve3Pool.revertNewParameters,
    Curve3Pool.commitTransferOwnership, Curve3Pool.applyTransferOwnership,
    Curve3Pool.revertTransferOwnership, Curve3Pool.withdrawAdminFees,
    Curve3Pool.donateAdminFees, Curve3Pool.killMe, Curve3Pool.unkillMe] <;> opt_walk
  all_goals first
    | exact OptAll.none'
    | exact OptAll.some' hs
    | exact OptAll.some' ⟨hs.1, ‹_ ≤ maxFee›, hs.2.2.1, ‹_ ≤ maxAdminFee›⟩
    | exact OptAll.some' ⟨hs.2.1, hs.2.1, hs.2.2.2, hs.2.2.2⟩

theorem feesBounded_keeps : Curve3Pool.StepKeeps FeesBounded := by
  intro s e c o h hs
  exact body_feesBounded s e c hs o (Curve3Pool.pool_step_body h)

/-- **The pool's fee words are within their limits at a moment of mainnet.** -/
theorem Moment.feesWithin {d : Deployment} (m : Moment d) (A : Assumes d m.through) :
    word m.world pool Curve3Pool.feeSlot ≤ feeDen ∧ word m.world pool Curve3Pool.adminFeeSlot ≤ feeDen := by
  obtain ⟨hpool, -, invs₀, ps, cs, -, -, -, run₀, -, -, joint⟩ :=
    Curve3PoolJointRoot.joint_root_replay (Deployment.toJoint d A.facts)
  obtain ⟨hcoins, htoken⟩ := run₀.coins_token
  have envAt : Curve3Pool.PoolMidEnv (d.sinceC3Block m.through) ((d.sinceMinter m.history).step m.block)
      pool ps.coins ps.token := by
    rw [hcoins, htoken]
    exact A.env
  obtain ⟨-, invs, -, -, -, s, run, -, hck, -, -⟩ :=
    Curve3Pool.pool_window_history (d.sinceMinter m.history) m.block m.cut hpool joint.poolCk envAt
  have h0 : FeesBounded (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) := by
    simp only [FeesBounded, Curve3Pool.Creation.poolInitState, Curve3Pool.maxFee, Curve3Pool.maxAdminFee]
    decide
  have hb := Curve3Pool.PoolRun.keeps feesBounded_keeps run (Curve3Pool.PoolRun.keeps feesBounded_keeps run₀ h0)
  have e1 : word m.world pool Curve3Pool.feeSlot = s.fee := hck.abs.fee
  have e2 : word m.world pool Curve3Pool.adminFeeSlot = s.adminFee := hck.abs.adminFee
  rw [e1, e2]
  obtain ⟨b1, -, b3, -⟩ := hb
  simp only [Curve3Pool.maxFee, Curve3Pool.maxAdminFee, feeDen] at b1 b3 ⊢
  omega

/-! ## The model -/

/-- The product of a value and a word's scale, under a scale of `10 ^ 18` times `m`: what's paid back of a scaled amount. -/
theorem out_add_admin {m d f q xj b : Nat} (hm : 0 < m) (hx : xj = m * b) (hd : d + 1 ≤ xj) (hf : f ≤ d) (hq : q ≤ f) :
    (d - f) / m + q / m + 1 ≤ b := by
  have h1 : (d - f) / m + q / m ≤ (d - f + q) / m := Nat.add_div_le_add_div _ _ _
  have h2 : (d - f + q) / m ≤ d / m := Nat.div_le_div_right (by omega)
  have h3 : d / m < b := by
    rw [Nat.div_lt_iff_lt_mul hm, Nat.mul_comm]
    omega
  omega

/-- What the curve's quote unfolds to. -/
theorem swapOut_parts {w : State} {t : Nat} {i j : Fin 3} {dx dy : Nat} (h : swapOut w t i j dx = some dy) :
    ∃ amp x y d1 d p f, ampAt w t = some amp ∧
      chkMul (netOf w i dx) (rates.get i) = some x ∧ chkDiv x precision = some p ∧ chkAdd (scaled w i) p = some y ∧
      getYChk amp i j y (scaled w) = some d1 ∧ chkSub (scaled w j) d1 = some d ∧
      (∃ d2 p2, chkSub d 1 = some d2 ∧ chkMul d2 (word w pool Curve3Pool.feeSlot) = some p2 ∧ chkDiv p2 feeDen = some f ∧
        dy = (d2 - f) * precision / rates.get j ∧
        swapAdmin w t i j dx = some ((f * word w pool Curve3Pool.adminFeeSlot / feeDen) * precision / rates.get j)) := by
  unfold swapOut at h
  obtain ⟨⟨q1, q2⟩, hq, hdy⟩ := Option.map_eq_some_iff.1 h
  have hq0 := hq
  unfold swapQuote at hq
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨x, hx, p, hp, y, hy, amp, hamp, d1, hd1, d, hd, d2, hd2, p2, hp2, f, hf, rfl, rfl⟩ := hq
  refine ⟨amp, x, y, d1, d, p, f, hamp, hx, hp, hy, hd1, hd, d2, p2, hd2, hp2, hf, hdy.symm, ?_⟩
  simp only [swapAdmin, hq0, Option.map_some]

/-- A word's value at a coin's rate, in its decimals. -/
theorem div_rate (a : Nat) (j : Fin 3) : a * precision / rates.get j = a / Curve3Pool.precMul.get j := by
  match j with
  | 0 => exact (Nat.mul_div_cancel _ (by decide)).trans (Nat.div_one a).symm
  | 1 => exact Nat.mul_div_mul_right a (10 ^ 12) (by decide : 0 < 10 ^ 18)
  | 2 => exact Nat.mul_div_mul_right a (10 ^ 12) (by decide : 0 < 10 ^ 18)

theorem precMul_pos (j : Fin 3) : 0 < Curve3Pool.precMul.get j := by
  match j with
  | 0 => decide
  | 1 => decide
  | 2 => decide

theorem rates_ne (j : Fin 3) : rates.get j ≠ 0 := by
  match j with
  | 0 => decide
  | 1 => decide
  | 2 => decide

/-- The numbers a swap the curve quotes comes to. -/
structure SwapWords (w : State) (i j : Fin 3) (net y d2 f dy admin : Nat) : Prop where
  /-- `get_y`'s answer at the new balance. -/
  got : scaled w j = y + d2 + 1
  /-- The fee, on the output less one. -/
  fee : f = d2 * word w pool Curve3Pool.feeSlot / feeDen
  /-- The output in the coin's own units. -/
  out : dy = (d2 - f) * precision / rates.get j
  /-- The admin's cut in the coin's own units. -/
  cut : admin = (f * word w pool Curve3Pool.adminFeeSlot / feeDen) * precision / rates.get j
  /-- What's paid and cut leaves the books positive. -/
  room : dy + admin + 1 ≤ recorded w j
  /-- The fee is within the output. -/
  feeLe : f ≤ d2

/-- **The model accepts the swap the curve quotes.** -/
theorem exchange_accepts {w : State} {s : Curve3Pool.State} {e : Env} {i j : Fin 3} {dx dy minDy amp D : Nat}
    (hab : Curve3Pool.Abstracts (w.getStor pool) s) (hk : s.isKilled = false) (hd : i ≠ j)
    (hnet : pullIn e i dx = some (netOf w i dx)) (hinv : invariant w amp = some D) (hA : ampAt w e.time = some amp)
    (hfee : word w pool Curve3Pool.feeSlot ≤ feeDen) (haf : word w pool Curve3Pool.adminFeeSlot ≤ feeDen)
    (hq : swapOut w e.time i j dx = some dy) (hmin : minDy ≤ dy) (hfit : scaled w j < 2 ^ 190)
    (hbi : recorded w i + netOf w i dx < 2 ^ 256) (hpush : (e.coin j).pushOk = true) :
    ∃ o admin y d2 f, Curve3Pool.exchange s e i j dx minDy = some o ∧ Curve3Pool.exPushAmt o = dy ∧
      swapAdmin w e.time i j dx = some admin ∧ getYChk amp i j (scaled w i + netOf w i dx * rates.get i / precision) (scaled w) = some y ∧
      SwapWords w i j (netOf w i dx) y d2 f dy admin := by
  have hbk : books w = s.balances := books_of_abstracts hab
  have hS : ∀ k, scaled w k = Curve3Pool.precMul.get k * recorded w k := fun k => by
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  obtain ⟨xp, hxp, -⟩ : ∃ xp, xpChk (books w) = some xp ∧ Blanc.StableSwapNewton.getDChk xp.get amp 1 = some D := by
    unfold invariant Curve3Pool.getDMem at hinv
    simpa only [Option.bind_eq_bind, Option.bind_eq_some_iff] using hinv
  have hxg : xp.get = scaled w := Curve3Pool.xpChk_some hxp
  rw [hbk] at hxp
  obtain ⟨amp', x, y, d1, d, p, f, hamp, hx, hp, hy, hd1, hd', d2, p2, hd2, hp2, hf, hdy, hadm⟩ := swapOut_parts hq
  obtain rfl : amp' = amp := Option.some.inj (hamp.symm.trans hA)
  have hA' : aChk s e.time = some amp' := by rw [← ampAt_of_abstracts hab]; exact hamp
  have ex : x = netOf w i dx * rates.get i := Blanc.StableSwapNewton.chkMul_some hx
  have ep := (Blanc.StableSwapNewton.chkDiv_some hp).1
  have ey := Blanc.StableSwapNewton.chkAdd_some hy
  obtain ⟨ed, hle1⟩ := Blanc.StableSwapNewton.chkSub_some hd'
  obtain ⟨ed2, hle2⟩ := Blanc.StableSwapNewton.chkSub_some hd2
  have ep2 := Blanc.StableSwapNewton.chkMul_some hp2
  have ef := (Blanc.StableSwapNewton.chkDiv_some hf).1
  have hsf : word w pool Curve3Pool.feeSlot = s.fee := hab.fee
  have hsa : word w pool Curve3Pool.adminFeeSlot = s.adminFee := hab.adminFee
  have hf2 : f = d2 * word w pool Curve3Pool.feeSlot / feeDen := by rw [ef, ep2]
  have hfd : f ≤ d2 := by
    rw [hf2]
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hfee)
  have hd2x : d2 + 1 ≤ scaled w j := by omega
  have hd190 : d2 < 2 ^ 190 := by omega
  have hfeeDen : feeDen = 10000000000 := rfl
  have hprec : precision = 1000000000000000000 := rfl
  have hq0 : f * word w pool Curve3Pool.adminFeeSlot / feeDen ≤ f :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ haf)
  obtain ⟨q, hqd⟩ : ∃ q, q = f * word w pool Curve3Pool.adminFeeSlot / feeDen := ⟨_, rfl⟩
  rw [← hqd] at hq0
  have hbound := out_add_admin (m := Curve3Pool.precMul.get j) (b := recorded w j) (precMul_pos j) (hS j) hd2x hfd hq0
  rw [← div_rate, ← div_rate, ← hdy] at hbound
  obtain ⟨A, hAd⟩ : ∃ A, A = q * precision / rates.get j := ⟨_, rfl⟩
  rw [← hAd] at hbound
  have hm1 : d2 - f < 2 ^ 190 := by omega
  have hm2 : (d2 - f) * precision < 2 ^ 256 := by
    rw [hprec]
    have : (1000000000000000000 : Nat) < 2 ^ 60 := by decide
    calc (d2 - f) * 1000000000000000000 ≤ (2 ^ 190) * 2 ^ 60 := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 256 := by decide
  have hfa : f * s.adminFee < 2 ^ 256 := by
    rw [← hsa]
    calc f * word w pool Curve3Pool.adminFeeSlot ≤ (2 ^ 190) * 2 ^ 40 := Nat.mul_le_mul (by omega) (by rw [hfeeDen] at haf; omega)
      _ < 2 ^ 256 := by decide
  have hqa : q * precision < 2 ^ 256 := by
    rw [hprec]
    calc q * 1000000000000000000 ≤ (2 ^ 190) * 2 ^ 60 := Nat.mul_le_mul (by omega) (by decide)
      _ < 2 ^ 256 := by decide
  have hsj : s.balances.get j = recorded w j := (recorded_of_abstracts hab j).symm
  have hsi : s.balances.get i = recorded w i := (recorded_of_abstracts hab i).symm
  have ey' : y = scaled w i + netOf w i dx * rates.get i / precision := by rw [ey, ep, ex]
  obtain ⟨o, ho⟩ : ∃ o, o = (⟨{ s with balances := V3.set (V3.set s.balances i (recorded w i + netOf w i dx)) j (recorded w j - ((d2 - f) * precision / rates.get j) - (q * precision / rates.get j)) }, none,
      [.tokenExchange e.caller i.val dx j.val ((d2 - f) * precision / rates.get j)],
      [.pull i e.caller dx, .push j e.caller ((d2 - f) * precision / rates.get j)]⟩ : Out) := ⟨_, rfl⟩
  refine ⟨o, q * precision / rates.get j, d1, d2, f, ?_, ?_, ?_, ?_, ?_⟩
  · have r2 : chkMul (netOf w i dx) (rates.get i) = some x := hx
    have r3 : chkAdd (xp.get i) p = some y := by rw [hxg]; exact hy
    have r4 : getYChk amp' i j y xp.get = some d1 := by rw [hxg]; exact hd1
    have r5 : chkSub (xp.get j) d1 = some d := by rw [hxg]; exact hd'
    have r6 : chkMul d2 s.fee = some p2 := by rw [← hsf]; exact hp2
    have r7 : chkSub d2 f = some (d2 - f) := ite_eq_left hfd
    have r8 : chkMul (d2 - f) precision = some ((d2 - f) * precision) := ite_eq_left hm2
    have r9 : chkDiv ((d2 - f) * precision) (rates.get j) = some ((d2 - f) * precision / rates.get j) := ite_eq_right (rates_ne j)
    have r11 : chkMul f s.adminFee = some (f * s.adminFee) := ite_eq_left hfa
    have r12 : chkDiv (f * s.adminFee) feeDen = some q := by rw [hqd, hsa]; exact ite_eq_right (by decide)
    have r13 : chkMul q precision = some (q * precision) := ite_eq_left hqa
    have r14 : chkDiv (q * precision) (rates.get j) = some (q * precision / rates.get j) := ite_eq_right (rates_ne j)
    have r15 : chkAdd (s.balances.get i) (netOf w i dx) = some (recorded w i + netOf w i dx) := by
      rw [hsi]; exact ite_eq_left hbi
    have r16 : chkSub (s.balances.get j) ((d2 - f) * precision / rates.get j) = some (recorded w j - (d2 - f) * precision / rates.get j) := by
      rw [hsj, ← hdy]; exact ite_eq_left (by omega)
    have r17 : chkSub (recorded w j - (d2 - f) * precision / rates.get j) (q * precision / rates.get j) =
        some (recorded w j - (d2 - f) * precision / rates.get j - q * precision / rates.get j) := by
      rw [← hdy, ← hAd]; exact ite_eq_left (by omega)
    rw [ho]
    exact Curve3Pool.ex_model_eq hk hxp hnet r2 hp r3 hA' r4 r5 hd2 r6 hf r7 r8 r9 (by rw [← hdy]; exact hmin) r11 r12 r13 r14 r15 r16 r17 hpush
  · rw [ho, hdy]
    rfl
  · rw [hadm, hqd]
  · rw [← ey']; exact hd1
  · exact ⟨by omega, hf2, hdy, by rw [hqd], by rw [← hAd]; omega, hfd⟩

section Args

variable {e : Sevm} {i j : Fin 3} {dx minDy : Nat}

theorem swapCalldata_length : (swapCalldata i j dx minDy).length = 132 := by
  simp only [swapCalldata, Curve3Pool.word, List.length_append, B256.length_toBytes, abiSelectorBytes_length]

/-- `swapCalldata`'s selector. -/
theorem swap_selector (h : e.data = swapCalldata i j dx minDy) : Sevm.selector e = Curve3Pool.selExchange := by
  refine selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
    (tail := Curve3Pool.word i ++ Curve3Pool.word j ++ Curve3Pool.word dx ++ Curve3Pool.word minDy) ?_
  rw [h]
  simp only [swapCalldata, List.append_assoc]

/-- `swapCalldata`'s four words. -/
theorem swap_words (h : e.data = swapCalldata i j dx minDy) :
    Sevm.dataWord e 4 = Nat.toB256 i ∧ Sevm.dataWord e 36 = Nat.toB256 j ∧
      Sevm.dataWord e 68 = Nat.toB256 dx ∧ Sevm.dataWord e 100 = Nat.toB256 minDy := by
  have l4 := abiSelectorBytes_length Curve3Pool.selExchange
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selExchange)
      (rest := Curve3Pool.word j ++ Curve3Pool.word dx ++ Curve3Pool.word minDy) ?_ (by rw [l4]; rfl)
    rw [h]; simp only [swapCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selExchange ++ Curve3Pool.word i)
      (rest := Curve3Pool.word dx ++ Curve3Pool.word minDy) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [swapCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selExchange ++ Curve3Pool.word i ++ Curve3Pool.word j)
      (rest := Curve3Pool.word minDy) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [swapCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selExchange ++ Curve3Pool.word i ++ Curve3Pool.word j ++
        Curve3Pool.word dx) (rest := []) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [swapCalldata, Curve3Pool.word, List.append_assoc, List.append_nil]

end Args

end Blanc.Composition.Curve3PoolPublic
