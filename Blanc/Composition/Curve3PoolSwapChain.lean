import Blanc.Composition.Curve3PoolSwapEval

/-!
# `exchange`'s canonical chain from a cold start

`SwapChain.eval`: the frame's exact cost is `swapFrameGas`, and its end has `swapRefund` and `SwapPaid`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (swapCalls swapPullD swapPullN swapPushD swapPushN swapB1 swapB2)

/-- What `rx_ex_frame_floor`'s continuation is told about the frame's end and its call sites. -/
def ExFrameEnd (sevm : Sevm) (pre : Devm) (P : ExchangeExactCalls) (x0 x1 x2 B1 B2 : B256) (v : Nat) (D' : Devm) : Prop :=
  ExEnd sevm (exTailN2 sevm (afterSload sevm (aBase sevm (exPath sevm pre P x0 x1 x2 B1 B2).n) (Bytes.toB256 [0x02]))
      (exBackDyMem sevm (exPath sevm pre P x0 x1 x2 B1 B2).M ((pre.getStor sevm.currentTarget).set lockSlot 1)
        (exW3 x0 x1 x2) (exPath sevm pre P x0 x1 x2 B1 B2).D v)
      ((pre.getStor sevm.currentTarget).set lockSlot 1)
      (exW3 (balAt (pre.getStor sevm.currentTarget) 0) (balAt (pre.getStor sevm.currentTarget) 1)
        (balAt (pre.getStor sevm.currentTarget) 2)) (exPath sevm pre P x0 x1 x2 B1 B2).D
      (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot))
      (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)))
    (exStoreI2 (exBackDyMem sevm (exPath sevm pre P x0 x1 x2 B1 B2).M ((pre.getStor sevm.currentTarget).set lockSlot 1)
        (exW3 x0 x1 x2) (exPath sevm pre P x0 x1 x2 B1 B2).D v) sevm
      (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot)
      (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)))
    P.pushN D' ∧
  ExPushWin sevm (exStoreI2 (exBackDyMem sevm (exPath sevm pre P x0 x1 x2 B1 B2).M ((pre.getStor sevm.currentTarget).set lockSlot 1)
        (exW3 x0 x1 x2) (exPath sevm pre P x0 x1 x2 B1 B2).D v) sevm
      (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot)
      (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)))
    (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)) ∧
  ExFrontWins sevm pre P x0 x1 x2 B1

/-- What the chain's evaluation stands on. -/
structure SwapChain (s : Sevm) (p : Devm) (w : Jaune.State) (E : Adr) (i j : Fin 3) (dx dy admin : Nat)
    (x0 x1 x2 B1 B2 F O A : B256) (amp v xv DD : Nat) : Prop where
  back : SwapBack s p w E i j (exCred s B1 B2) O A dy
  apart : SwapApart w E
  coinI : ((lockedStor w).get (coinsBase + Nat.toB256 i.val)).toAdr = coinAt i
  dxw : exDx s = Nat.toB256 dx
  hF : exDyFee (exW3 x0 x1 x2 (exJ s).toNat) (Nat.toB256 v) ((w.getStor pool).get feeSlot) = F
  hO : exDyOut (exW3 x0 x1 x2 (exJ s).toNat) (Nat.toB256 v) ((w.getStor pool).get feeSlot) (exRate (exJ s).toNat) = O
  hA : exAdm F ((w.getStor pool).get adminFeeSlot) (exRate (exJ s).toNat) = A
  Dn : (exCred s B1 B2).toNat = netOf w i dx
  On : O.toNat = dy
  An : A.toNat = admin
  holds : dx ≤ coinHeld w E i ∧ dx ≤ allowanceOf w E i
  creditP : CreditFits w pool i (netOf w i dx)
  feeI : i = 2 → UsdtFeeFits w dx
  moved : 0 < dx ∧ 0 < dy
  hY : ∀ b, costGetY s b amp (exI s).toNat (exJ s).toNat (exXw s (exW3 x0 x1 x2) (exCred s B1 B2)).toNat (exW3 x0 x1 x2 0).toNat (exW3 x0 x1 x2 1).toNat
    (exW3 x0 x1 x2 2).toNat = 2100 + aGas s b + newtonGas w amp i j xv DD

variable {s : Sevm} {p : Devm} {w : Jaune.State} {E : Adr} {i j : Fin 3} {dx dy admin : Nat}
  {x0 x1 x2 B1 B2 F O A : B256} {amp v xv DD : Nat}

theorem SwapChain.not_max (c : SwapChain s p w E i j dx dy admin x0 x1 x2 B1 B2 F O A amp v xv DD) : dx ≠ 2 ^ 256 - 1 := by
  intro e
  have hcp : word w (coinAt i) (coinEntry pool i) + netOf w i dx < 2 ^ 255 := c.creditP
  by_cases hi : i = 2
  · subst hi
    obtain ⟨hff, -, hfl⟩ := c.feeI rfl
    have hn : netOf w 2 dx = dx - usdtFee w dx := rfl
    have hr : word w usdt 3 ≤ 1 := by
      rcases Nat.lt_or_ge 1 (word w usdt 3) with h | h
      · have : dx * 2 ≤ dx * word w usdt 3 := Nat.mul_le_mul_left _ h
        rw [e] at this hff
        omega
      · exact h
    have hq : dx * word w usdt 3 / 10000 ≤ 2 ^ 256 / 10000 := Nat.div_le_div_right (by
      rw [e]
      calc (2 ^ 256 - 1) * word w usdt 3 ≤ (2 ^ 256 - 1) * 1 := Nat.mul_le_mul_left _ hr
        _ ≤ 2 ^ 256 := by decide)
    have hfq : usdtFee w dx ≤ dx * word w usdt 3 / 10000 := Nat.min_le_left _ _
    have : (2 : Nat) ^ 256 / 10000 < 2 ^ 250 := by decide
    rw [hn] at hcp
    omega
  · have hn : netOf w i dx = dx := by unfold netOf; rw [ite_eq_right hi]
    rw [hn] at hcp
    omega

/-- The refund: an unlimited allowance's word is never emptied by a swap. -/
theorem SwapChain.allow_refund (c : SwapChain s p w E i j dx dy admin x0 x1 x2 B1 B2 F O A amp v xv DD) (al : Nat) :
    allowEmpties al dx = empties al dx := by
  unfold allowEmpties
  split
  · rename_i h
    have := c.not_max
    exact (ite_eq_right (fun e => absurd (by omega) this)).symm
  · rfl

theorem coinT_apart : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ coinT j, x ∉ [pool] ++ coinT i := by decide

theorem coinAt_apart : ∀ i j : Fin 3, i ≠ j → coinAt i ≠ pool ∧ coinAt i ∉ coinT j := by decide

theorem exW3_get (a b c : B256) : ∀ k : Fin 3, exW3 a b c k.val = (if k = 0 then a else if k = 1 then b else c) := by
  intro k
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- **From the base the pull leaves**: the back half's cost, the refund and the effect. -/
theorem SwapChain.finish (c : SwapChain s p w E i j dx dy admin x0 x1 x2 B1 B2 F O A amp v xv DD) {n : Devm} {M : Mem} {c0 : Nat}
    {Tn : List Adr} {rn : Int} {D' : Devm}
    (hA : At s.currentTarget (headK i.val) (lockedStor w) n) (mv : Mv Tn rn p n) (hT : ∀ x ∈ coinT j, x ∉ Tn)
    (hPi : n.getStor (coinAt i) = pulledAll w E i dx)
    (hEnd : ExEnd s (exTailN2 s (afterSload s (aBase s n) (Bytes.toB256 [0x02])) (exBackDyMem s M (lockedStor w) (exW3 x0 x1 x2) (exCred s B1 B2) v)
        (lockedStor w) (exW3 (balAt (w.getStor pool) 0) (balAt (w.getStor pool) 1) (balAt (w.getStor pool) 2)) (exCred s B1 B2) F O)
      (exStoreI2 (exBackDyMem s M (lockedStor w) (exW3 x0 x1 x2) (exCred s B1 B2) v) s F ((lockedStor w).get adminFeeSlot) O)
      (swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) D')
    (win : ExPushWin s (exStoreI2 (exBackDyMem s M (lockedStor w) (exW3 x0 x1 x2) (exCred s B1 B2) v) s F ((lockedStor w).get adminFeeSlot) O) O) :
    exBackCost s n M c0 (lockedStor w) (exW3 (balAt (w.getStor pool) 0) (balAt (w.getStor pool) 1) (balAt (w.getStor pool) 2)) (exW3 x0 x1 x2)
        (exCred s B1 B2) amp v (swapPushD s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j)
        (swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) =
      279 + c0 + 3540 + (3906 + (2100 + (4285 + rampReadGas w s.benvStat.time.toNat) + newtonGas w amp i j xv DD)) + (612 + 2100) +
        (1225 + (2100 + creditG (recorded w i) (netOf w i dx) + 2900) +
          (2340 + 2100 + (2600 + 10 + 10688 + pushGas w E j dy) + 100)) ∧
    Mv (Tn ++ pool :: coinT j) (rn + ((4800 * empties (rawHeld w pool j) dy : Nat) : Int) + 19900) p D' ∧
      SwapPaid w D'.state E i j dx dy admin := by
  have g := c.back
  have f := g.stand
  have hL : ∀ k, k ≠ lockW → (lockedStor w).get k = (w.getStor pool).get k := fun k hk => Stor.get_set_ne _ (Ne.symm hk) _
  have hF0 : (lockedStor w).get feeSlot = (w.getStor pool).get feeSlot := hL _ (by decide)
  have hA0 : (lockedStor w).get adminFeeSlot = (w.getStor pool).get adminFeeSlot := hL _ (by decide)
  have hBK : ∀ k : Fin 3, ∀ K : B256, K = Nat.toB256 k.val → exW3 (balAt (w.getStor pool) 0) (balAt (w.getStor pool) 1) (balAt (w.getStor pool) 2) K.toNat =
      (lockedStor w).get (balancesBase + Nat.toB256 k.val) := fun k K hK => by
    subst hK
    rw [hL _ (bal_ne_lockW k)]
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have hrec : ∀ k : Fin 3, ((lockedStor w).get (balancesBase + Nat.toB256 k.val)).toNat = recorded w k := fun k => by
    rw [hL _ (bal_ne_lockW k)]; rfl
  obtain ⟨hc, hrest⟩ := swap_back (c0 := c0) (F := F) (B := exW3 (balAt (w.getStor pool) 0) (balAt (w.getStor pool) 1) (balAt (w.getStor pool) 2))
    (X := exW3 x0 x1 x2) (amp := amp) (v := v) (nw := newtonGas w amp i j xv DD) (M := M) g (hBK i _ g.iw) (hBK j _ g.jw) (by rw [hF0]; exact c.hF)
    (by rw [hF0]; exact c.hO) (by rw [hA0]; exact c.hA) hA mv hT c.hY win
  have hsum : (O + A).toNat = dy + admin := by
    have hb := g.below
    have hlt := B256.toNat_lt ((lockedStor w).get (balancesBase + Nat.toB256 j.val))
    rw [toNat_add_of (by omega), c.On, c.An]
  have hb := g.below
  rw [hrec j, c.On, c.An] at hb
  have hd0 := c.moved.2
  have hdb : debitG (O + A).toNat = 2900 := by
    unfold debitG
    rw [hsum, ite_eq_right (by omega)]
  have hcr := g.credit
  rw [hrec i, c.Dn] at hcr
  obtain ⟨mD, hsP, hsJ, hsO⟩ := hrest D' hEnd
  have hdxLt : dx < 2 ^ 256 := Nat.lt_of_le_of_lt c.holds.1 coinHeld_lt
  have hdyLt : dy < 2 ^ 256 := Nat.lt_of_le_of_lt g.pays.1 coinHeld_lt
  have hpi : D'.getStor (coinAt i) = pulledAll w E i dx := by
    obtain ⟨h1, h2⟩ := coinAt_apart i j g.differ
    rw [hsO _ h1 h2, hPi]
  refine ⟨?_, mD, ?_⟩
  · rw [hc, hrec i, c.Dn, hdb]
    have hg := gas_push w E j hd0 (fun h => (g.pays.2.2 h).2.2)
    omega
  · exact swap_paid f.open' c.apart hsP hpi hsJ g.differ c.Dn c.On c.An (by omega) (by omega) hdxLt hdyLt c.holds.1 g.pays.1 c.creditP g.pays.2.1 c.feeI g.pays.2.2

theorem fin_word_ne : ∀ i : Fin 3, i ≠ 2 → Nat.toB256 i.val ≠ (2 : B256) := by decide

theorem exI_ne_two {s : Sevm} {i : Fin 3} (hw : exI s = Nat.toB256 i.val) (hi : i ≠ 2) : exI s ≠ 2 := by
  rw [hw]
  exact fin_word_ne i hi

theorem exI_two {s : Sevm} (hw : exI s = Nat.toB256 (2 : Fin 3).val) : exI s = 2 := by rw [hw]; decide

/-- The storage the chain reads, while the lock is held, at the entry's facts. -/
theorem chain_stor (f : CoinStand s p w E) : p.getStor s.currentTarget = w.getStor pool ∧ (w.getStor pool).set lockSlot 1 = lockedStor w := by
  refine ⟨by rw [f.target]; exact (f.stor pool (Or.inl rfl)).1, ?_⟩
  rw [show lockSlot = lockW by decide, show (1 : B256) = Bytes.toB256 [1] by decide]

theorem coin_ne_lockW : ∀ k : Fin 3, coinsBase + Nat.toB256 k.val ≠ lockW := by decide

/-- The chain's coin word, under the lock. -/
theorem chain_coin {w : Jaune.State} (k : Fin 3) : (w.getStor pool).get (coinSlot k) = (lockedStor w).get (coinsBase + Nat.toB256 k.val) :=
  (Stor.get_set_ne _ (Ne.symm (coin_ne_lockW k)) _).symm

theorem pulled_all_a (w : Jaune.State) (E : Adr) (i : Fin 3) (hi : i ≠ 2) (dx : Nat) : pulledStor w E i dx = pulledAll w E i dx := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => exact absurd rfl hi

theorem pullAR_eq (w : Jaune.State) (E : Adr) (i : Fin 3) (hi : i ≠ 2) (dx : Nat) (h : allowEmpties (allowanceOf w E i) dx = empties (allowanceOf w E i) dx) :
    pullAR w E i dx = empties (rawHeld w E i) dx + empties (allowanceOf w E i) dx := by
  match i with
  | 0 =>
    show allowEmpties (allowanceOf w E 0) dx + empties (rawHeld w E 0) dx = _
    rw [h, Nat.add_comm]
  | 1 => exact Nat.add_comm _ _
  | 2 => exact absurd rfl hi

/-- **DAI or USDC pulled**: the cost and the end. -/
theorem SwapChain.eval_a (c : SwapChain s p w E i j dx dy admin x0 x1 x2 B1 B2 F O A amp v xv DD) (hi : i ≠ 2) {D' : Devm}
    (he : ExFrameEnd s p (swapCalls s p i j) x0 x1 x2 B1 B2 v D') :
    exExactCost s p (swapCalls s p i j) x0 x1 x2 B1 B2 amp v =
        swapFrameGas w E s.benvStat.time.toNat amp i j dx dy xv DD (decide (allowanceOf w E i = 2 ^ 256 - 1)) ∧
      ∃ T r, Mv T r p D' ∧ r = ((swapRefund w E i j dx dy (allowanceOf w E i) : Nat) : Int) ∧ SwapPaid w D'.state E i j dx dy admin := by
  have f := c.back.stand
  obtain ⟨hpS, hσ⟩ := chain_stor f
  have hne2 := exI_ne_two c.back.iw hi
  have hC : exCred s B1 B2 = exDx s := ite_eq_right hne2
  have hpath : exPath s p (swapCalls s p i j) x0 x1 x2 B1 B2 = ⟨exPullTail s (exN2 s p) (exM2 s p x0 x1 x2) (swapCalls s p i j).pullN,
      exPullMem s (exN2 s p) (exM2 s p x0 x1 x2) (swapCalls s p i j).pullN, 26, exDx s⟩ := ite_eq_right hne2
  obtain ⟨hEnd, hPush, hWins⟩ := he
  have hA0 : (lockedStor w).get adminFeeSlot = (w.getStor pool).get adminFeeSlot := Stor.get_set_ne _ (by decide) _
  rw [hpath, hpS, hσ, c.hF, c.hO, ← hA0] at hEnd hPush
  have hPN : (swapCalls s p i j).pushN = swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j := by
    show swapPushN s ((p.getStor s.currentTarget).get (coinSlot j)) j = _
    rw [hpS, chain_coin j]
  have hPD : (swapCalls s p i j).pushD = swapPushD s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j := by
    show swapPushD s ((p.getStor s.currentTarget).get (coinSlot j)) j = _
    rw [hpS, chain_coin j]
  rw [hPN] at hEnd
  obtain ⟨tI, htI⟩ : ∃ t, t = (lockedStor w).get (coinsBase + Nat.toB256 i.val) := ⟨_, rfl⟩
  have hPlD : (swapCalls s p i j).pullD = swapPullD s tI i := by
    show swapPullD s ((p.getStor s.currentTarget).get (coinSlot i)) i = _
    rw [hpS, chain_coin i, htI]
  have hPlN : (swapCalls s p i j).pullN = swapPullN s tI i := by
    show swapPullN s ((p.getStor s.currentTarget).get (coinSlot i)) i = _
    rw [hpS, chain_coin i, htI]
  rw [hPlN] at hEnd hPush
  obtain ⟨hhc, mh, ah⟩ := swap_head f c.back.lock c.back.iw
  have hn : netOf w i dx = dx := by unfold netOf; rw [ite_eq_right hi]
  have hdxLt : dx < 2 ^ 256 := Nat.lt_of_le_of_lt c.holds.1 coinHeld_lt
  have hcP : CreditFits w pool i dx := by rw [← hn]; exact c.creditP
  obtain ⟨fc, fm, fa, fs⟩ := front_nofee f c.apart hi (n := exN2 s p) (M := exM2 s p x0 x1 x2) (t := tI) c.dxw (by rw [htI]; exact c.coinI) (hWins.2 hne2) mh ah hdxLt c.holds.1 c.holds.2 hcP
  have hfin := c.finish (c0 := 26) fa fm (coinT_apart i j c.back.differ)
    (by
      rw [fs]
      exact pulled_all_a w E i hi dx)
    (by rw [hC]; exact hEnd) (by rw [hC]; exact hPush)
  obtain ⟨hb, hm, hpaid⟩ := hfin
  refine ⟨?_, _, _, hm, ?_, hpaid⟩
  · unfold exExactCost
    rw [ite_eq_right hne2, hhc, hPlD, hPlN, fc]
    have hbk : exNoFeeBackCost s p (swapCalls s p i j) x0 x1 x2 amp v = exBackCost s (exPullTail s (exN2 s p) (exM2 s p x0 x1 x2) (swapPullN s tI i))
        (exPullMem s (exN2 s p) (exM2 s p x0 x1 x2) (swapPullN s tI i)) 26 (lockedStor w)
        (exW3 (balAt (w.getStor pool) 0) (balAt (w.getStor pool) 1) (balAt (w.getStor pool) 2)) (exW3 x0 x1 x2) (exCred s B1 B2) amp v
        (swapPushD s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) (swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) := by
      unfold exNoFeeBackCost
      rw [hpS, hσ, hC, hPlN, hPD, hPN]
    rw [hbk, hb, hn]
    have hg := gas_pull_a w E hi c.moved.1
    unfold swapFrameGas
    rw [← hg]
    omega
  · have hAR : pullAR w E i dx = empties (rawHeld w E i) dx + empties (allowanceOf w E i) dx := by
      exact pullAR_eq w E i hi dx (c.allow_refund _)
    unfold swapRefund
    rw [hAR]
    push_cast
    omega

/-- **USDT pulled**: the cost and the end. -/
theorem SwapChain.eval_t {j : Fin 3} {dx dy admin : Nat} (c : SwapChain s p w E 2 j dx dy admin x0 x1 x2 B1 B2 F O A amp v xv DD) {D' : Devm}
    (he : ExFrameEnd s p (swapCalls s p 2 j) x0 x1 x2 B1 B2 v D') :
    exExactCost s p (swapCalls s p 2 j) x0 x1 x2 B1 B2 amp v =
        swapFrameGas w E s.benvStat.time.toNat amp 2 j dx dy xv DD (decide (allowanceOf w E 2 = 2 ^ 256 - 1)) ∧
      ∃ T r, Mv T r p D' ∧ r = ((swapRefund w E 2 j dx dy (allowanceOf w E 2) : Nat) : Int) ∧ SwapPaid w D'.state E 2 j dx dy admin := by
  have f := c.back.stand
  obtain ⟨hpS, hσ⟩ := chain_stor f
  have hee : exI s = 2 := exI_two c.back.iw
  have hA0 : (lockedStor w).get adminFeeSlot = (w.getStor pool).get adminFeeSlot := Stor.get_set_ne _ (by decide) _
  have hC : exCred s B1 B2 = B2 - B1 := ite_eq_left hee
  obtain ⟨tI, htI⟩ : ∃ t, t = (lockedStor w).get (coinsBase + Nat.toB256 (2 : Fin 3).val) := ⟨_, rfl⟩
  have hTi : (p.getStor s.currentTarget).get (coinSlot 2) = tI := by rw [hpS, chain_coin 2, htI]
  have hP1 : (swapCalls s p 2 j).balN1 = coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440 := by
    show coinStaticNext (fun s p => Usdt.balP s p 0) s ((p.getStor s.currentTarget).get (coinSlot 2)) 0x3dc 0x24 0x440 = _
    rw [hTi]
  have hP2 : (swapCalls s p 2 j).balN2 = coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x71c 0x24 0x780 := by
    show coinStaticNext (fun s p => Usdt.balP s p 0) s ((p.getStor s.currentTarget).get (coinSlot 2)) 0x71c 0x24 0x780 = _
    rw [hTi]
  have hD1 : (swapCalls s p 2 j).balD1 = coinStaticDebit Usdt.balG s tI 0x3dc 0x24 0x440 := by
    show coinStaticDebit Usdt.balG s ((p.getStor s.currentTarget).get (coinSlot 2)) 0x3dc 0x24 0x440 = _
    rw [hTi]
  have hD2 : (swapCalls s p 2 j).balD2 = coinStaticDebit Usdt.balG s tI 0x71c 0x24 0x780 := by
    show coinStaticDebit Usdt.balG s ((p.getStor s.currentTarget).get (coinSlot 2)) 0x71c 0x24 0x780 = _
    rw [hTi]
  have hPlD : (swapCalls s p 2 j).pullD = swapPullD s tI 2 := by
    show swapPullD s ((p.getStor s.currentTarget).get (coinSlot 2)) 2 = _
    rw [hTi]
  have hPlN : (swapCalls s p 2 j).pullN = swapPullN s tI 2 := by
    show swapPullN s ((p.getStor s.currentTarget).get (coinSlot 2)) 2 = _
    rw [hTi]
  have hpath : exPath s p (swapCalls s p 2 j) x0 x1 x2 B1 B2 = ⟨exBal2Next s (exPullTail s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (swapCalls s p 2 j).balN1)
        (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (swapCalls s p 2 j).balN1) (swapCalls s p 2 j).pullN)
        (exPullMem s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (swapCalls s p 2 j).balN1)
          (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (swapCalls s p 2 j).balN1) (swapCalls s p 2 j).pullN) (swapCalls s p 2 j).balN2,
      exBal2Mem s (exPullTail s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (swapCalls s p 2 j).balN1)
        (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (swapCalls s p 2 j).balN1) (swapCalls s p 2 j).pullN)
        (exPullMem s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (swapCalls s p 2 j).balN1)
          (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (swapCalls s p 2 j).balN1) (swapCalls s p 2 j).pullN) B1 B2 (swapCalls s p 2 j).balN2,
      6, B2 - B1⟩ := ite_eq_left hee
  obtain ⟨hEnd, hPush, hWins⟩ := he
  obtain ⟨w1, w2, w3⟩ := hWins.1 hee
  rw [hP1] at w2
  rw [hP1, hPlN] at w3
  rw [hpath, hpS, hσ, c.hF, c.hO, ← hA0, hP1, hP2, hPlN] at hEnd hPush
  have hPN : (swapCalls s p 2 j).pushN = swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j := by
    show swapPushN s ((p.getStor s.currentTarget).get (coinSlot j)) j = _
    rw [hpS, chain_coin j]
  have hPD : (swapCalls s p 2 j).pushD = swapPushD s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j := by
    show swapPushD s ((p.getStor s.currentTarget).get (coinSlot j)) j = _
    rw [hpS, chain_coin j]
  rw [hPN] at hEnd
  obtain ⟨hhc, mh, ah⟩ := swap_head f c.back.lock c.back.iw
  have hdxLt : dx < 2 ^ 256 := Nat.lt_of_le_of_lt c.holds.1 coinHeld_lt
  obtain ⟨fc, fr⟩ := front_fee f c.apart (n := exN2 s p) (M := exM2 s p x0 x1 x2) (t := tI) (B1 := B1) c.dxw (by rw [htI]; exact c.coinI) mh ah w1 w2 w3 hdxLt c.holds.1 c.holds.2 c.creditP (c.feeI rfl)
  obtain ⟨fm, fa, fs⟩ := fr (B2 := B2)
  have hfin := c.finish (c0 := 6) fa fm
    (fun x hx hm => by
      have := coinT_apart 2 j c.back.differ x hx
      apply this
      simpa only [List.mem_append, List.not_mem_nil, or_false, or_self_right, or_assoc, or_self] using hm)
    (by rw [show coinAt 2 = usdt from rfl, fs]; rfl)
    (by rw [hC]; exact hEnd) (by rw [hC]; exact hPush)
  obtain ⟨hb, hm, hpaid⟩ := hfin
  refine ⟨?_, _, _, hm, ?_, hpaid⟩
  · unfold exExactCost
    rw [ite_eq_left hee, hhc, hD1, hP1, hPlD, hPlN, hD2, fc]
    have hbk : exFeeBackCost s p (swapCalls s p 2 j) x0 x1 x2 B1 B2 amp v = exBackCost s (exBal2Next s (exPullTail s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440))
        (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440)) (swapPullN s tI 2))
        (exPullMem s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440))
          (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440)) (swapPullN s tI 2))
        (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x71c 0x24 0x780))
      (exBal2Mem s (exPullTail s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440))
        (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440)) (swapPullN s tI 2))
        (exPullMem s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440))
          (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x3dc 0x24 0x440)) (swapPullN s tI 2)) B1 B2
        (coinStaticNext (fun s p => Usdt.balP s p 0) s tI 0x71c 0x24 0x780)) 6 (lockedStor w)
        (exW3 (balAt (w.getStor pool) 0) (balAt (w.getStor pool) 1) (balAt (w.getStor pool) 2)) (exW3 x0 x1 x2) (exCred s B1 B2) amp v
        (swapPushD s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) (swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) := by
      unfold exFeeBackCost
      rw [hpS, hσ, hC, hP1, hP2, hPlN, hPD, hPN]
    rw [hbk, hb]
    have hg := gas_pull_t w E c.moved.1 (c.feeI rfl).2.2
    unfold swapFrameGas
    rw [← hg]
    omega
  · have hal := c.allow_refund (allowanceOf w E 2)
    unfold swapRefund
    rw [hal]
    push_cast
    omega

/-- **The canonical chain's cost, refund and effect at a cold entry.** -/
theorem SwapChain.eval (c : SwapChain s p w E i j dx dy admin x0 x1 x2 B1 B2 F O A amp v xv DD) {D' : Devm}
    (he : ExFrameEnd s p (swapCalls s p i j) x0 x1 x2 B1 B2 v D') :
    exExactCost s p (swapCalls s p i j) x0 x1 x2 B1 B2 amp v =
        swapFrameGas w E s.benvStat.time.toNat amp i j dx dy xv DD (decide (allowanceOf w E i = 2 ^ 256 - 1)) ∧
      ∃ T r, Mv T r p D' ∧ r = ((swapRefund w E i j dx dy (allowanceOf w E i) : Nat) : Int) ∧ SwapPaid w D'.state E i j dx dy admin := by
  by_cases hi : i = 2
  · subst hi
    exact c.eval_t he
  · exact c.eval_a hi he

end Blanc.Composition.Curve3PoolPublic
