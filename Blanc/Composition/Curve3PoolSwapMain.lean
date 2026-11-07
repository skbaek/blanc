import Blanc.Composition.Curve3PoolExitMain
import Blanc.Composition.Curve3PoolSwapBound
import Blanc.Composition.Curve3PoolSwapRequest

/-!
# `swap`: the run, the message and the transaction

`swap_floor_run`: the frame's run at any residual `R ≥ 2201`, from the model's words and the coins' fits, ending as
`ExFrameEnd` says. `swap_model`: `exchange_accepts` as the frame's words. `swap_core`: the message under the moment's facts.
`swap_holds` and `swap_message_holds` close the two statements.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool
open Blanc.StableSwapNewton (getYChk)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins PullFitsK PushFitsK pulledK swapCalls swapB1 swapB2 exchange_coins_floor swapW0 swapW1)
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf)

/-- **The frame's run at any residual `R ≥ 2201`**, from the words the model's step gives. -/
theorem swap_floor_run {msg : Msg} {s0 : Curve3Pool.State} {i j : Fin 3} {amp v : Nat} {x0 x1 x2 : B256}
    (hcode : (initSevm msg).code = Curve3Pool.code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : 2 ≤ (initSevm msg).depth)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selExchange) (hid : IdReady (initSevm msg) (initDevm msg))
    (hC : RealCoins (initSevm msg) (initDevm msg)) (hij : i ≠ j)
    (hiw : i.val = (exI (initSevm msg)).toNat) (hjw : j.val = (exJ (initSevm msg)).toNat)
    (ha : Abstracts ((initDevm msg).getStor (initSevm msg).currentTarget) s0)
    (hlock : ((initDevm msg).getStor (initSevm msg).currentTarget).get lockSlot = 0) (hval : (initSevm msg).value = 0)
    (hkill : ((initDevm msg).getStor (initSevm msg).currentTarget).get isKilledSlot = 0)
    (hi3 : (exI (initSevm msg)).toNat < 3) (hj3 : (exJ (initSevm msg)).toNat < 3)
    (hX : xpChk ⟨(balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0).toNat,
      (balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1).toNat,
      (balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hsub : exI (initSevm msg) = 2 → ¬ swapB2 (initSevm msg) (initDevm msg) i < swapB1 (initSevm msg) (initDevm msg) i)
    (hpf : PullFitsK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).caller (initSevm msg).currentTarget (exDx (initSevm msg)))
    (hqf : PushFitsK j ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) j)) (initSevm msg).currentTarget (initSevm msg).caller
      (exDyOut (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) (exRate (exJ (initSevm msg)).toNat)))
    (hlive : i = 2 → Blanc.Lift.Usdt.NotDeprecated (pulledK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).caller
      (initSevm msg).currentTarget (exDx (initSevm msg))))
    (hmx : exCred (initSevm msg) (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) * exRate (exI (initSevm msg)).toNat / exCred (initSevm msg) (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) =
      exRate (exI (initSevm msg)).toNat ∨ exCred (initSevm msg) (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) = 0)
    (hax : ¬ exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) * exRate (exI (initSevm msg)).toNat / exR0 <
      exW3 x0 x1 x2 (exI (initSevm msg)).toNat)
    (hA : aChk s0 (initSevm msg).benvStat.time.toNat = some amp)
    (hres : getYChk amp ⟨(exI (initSevm msg)).toNat, hi3⟩ ⟨(exJ (initSevm msg)).toNat, hj3⟩
      (exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) * exRate (exI (initSevm msg)).toNat / exR0).toNat
      (V3.mk x0.toNat x1.toNat x2.toNat).get = some v)
    (hy1 : ¬ exW3 x0 x1 x2 (exJ (initSevm msg)).toNat < Nat.toB256 v)
    (hy2 : ¬ exW3 x0 x1 x2 (exJ (initSevm msg)).toNat - Nat.toB256 v < Bytes.toB256 [1])
    (hmf : exDy0 (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) *
        ((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot /
        exDy0 (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) =
        ((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot ∨
      exDy0 (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) = 0)
    (hsf : ¬ exDy0 (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) <
      exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
        (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot))
    (hmo : (exDy0 (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
          (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot)) * exR0 /
        (exDy0 (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) -
          exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
            (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot)) = exR0 ∨
      exDy0 (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
          (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) = 0)
    (hmin : ¬ exDyOut (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
      (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) (exRate (exJ (initSevm msg)).toNat) < exMinDy (initSevm msg))
    (hma : exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
        (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) *
        ((initDevm msg).getStor (initSevm msg).currentTarget).get adminFeeSlot /
        exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
          (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) =
        ((initDevm msg).getStor (initSevm msg).currentTarget).get adminFeeSlot ∨
      exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
        (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) = 0)
    (hmap : exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
        (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot))
        (((initDevm msg).getStor (initSevm msg).currentTarget).get adminFeeSlot) * exR0 /
        exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
          (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot))
          (((initDevm msg).getStor (initSevm msg).currentTarget).get adminFeeSlot) = exR0 ∨
      exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
        (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot))
        (((initDevm msg).getStor (initSevm msg).currentTarget).get adminFeeSlot) = 0)
    (hbi : ¬ exBal ((initDevm msg).getStor (initSevm msg).currentTarget) ⟨(exI (initSevm msg)).toNat, hi3⟩ + exCred (initSevm msg) (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) <
      exBal ((initDevm msg).getStor (initSevm msg).currentTarget) ⟨(exI (initSevm msg)).toNat, hi3⟩)
    (hbj1 : ¬ exBal ((initDevm msg).getStor (initSevm msg).currentTarget) ⟨(exJ (initSevm msg)).toNat, hj3⟩ <
      exDyOut (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
        (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) (exRate (exJ (initSevm msg)).toNat))
    (hbj2 : ¬ exBal ((initDevm msg).getStor (initSevm msg).currentTarget) ⟨(exJ (initSevm msg)).toNat, hj3⟩ -
        exDyOut (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
          (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) (exRate (exJ (initSevm msg)).toNat) <
      exAdm (exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v)
        (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot))
        (((initDevm msg).getStor (initSevm msg).currentTarget).get adminFeeSlot) (exRate (exJ (initSevm msg)).toNat))
    {R : Nat} (hR0 : 2201 ≤ R)
    (hGb : R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i)
      (swapB2 (initSevm msg) (initDevm msg) i) amp v < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2
        (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp v))) = .ok post ∧ post.gasLeft = R ∧
      ExFrameEnd {initSevm msg with gas := R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp v} (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2
        (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) v post := by
  have hdep0 : (initSevm msg).depth ≠ 0 := by omega
  have hci : coinSlot i = coinsBase + exI (initSevm msg) := by
    unfold coinSlot; rw [hiw, toB256_toNat]
  have hcj : coinSlot j = coinsBase + exJ (initSevm msg) := by
    unfold coinSlot; rw [hjw, toB256_toNat]
  obtain ⟨hW0c, hW1c, hW0, hTc, hbal, hpull, hpush⟩ := exchange_coins_floor (sevm := initSevm msg) (pre := initDevm msg) hfork hstatic hdepth hC hij hpf hqf hlive
  rw [hci] at hpull hbal
  rw [hcj] at hpush
  obtain ⟨F, hF⟩ : ∃ F, F = R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i)
      (swapB2 (initSevm msg) (initDevm msg) i) amp v := ⟨_, rfl⟩
  rw [← hF]
  have hcost := exExactCost_withStaticGas (initSevm msg) F (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i)
      (swapB2 (initSevm msg) (initDevm msg) i) amp v
  obtain ⟨r, hr, D, rfl, hDg, hend⟩ := rx_ex_frame_floor (sevm := {initSevm msg with gas := F}) (pre := initDevm msg) (s0 := s0) (R := R) (U := 129555) (amp := amp) (v := v)
    (x0 := x0) (x1 := x1) (x2 := x2) (B1 := swapB1 (initSevm msg) (initDevm msg) i) (B2 := swapB2 (initSevm msg) (initDevm msg) i)
    (Q := fun r => ∃ D', r = .halted D' ∧ D'.gasLeft = R ∧ ExFrameEnd {initSevm msg with gas := F} (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2
      (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) v D')
    (swapCalls (initSevm msg) (initDevm msg) i j) hfork hstatic hdep0 hlen hcd hsel (hid.withStaticGas F) (hW0c.withStaticGas F) (hW1c.withStaticGas F) hW0 ha hlock hval hkill hi3 hj3 hX
    (fun h2 => by
      have h2' : exI (initSevm msg) = 2 := h2
      have hb := hbal (Fin.ext (by rw [hiw, h2']; rfl))
      exact ⟨hb.1.withStaticGas F, hb.2.1, hb.2.2.1.withStaticGas F, hb.2.2.2, hsub h2⟩)
    (hpull.withStaticGas F) hmx hax hA hres hy1 hy2 hmf hsf hmo hmin hma hmap hbi hbj1 hbj2 (hTc.withStaticGas F) (hpush.withStaticGas F) hR0
    (by rw [hcost]; exact hGb) (fun D' _ hg a b c => ⟨D', rfl, hg, a, b, c⟩)
  rw [hcost, ← hF] at hr
  obtain ⟨exD⟩ := Lift.lift_exactM (sevm := {initSevm msg with gas := F}) Curve3Pool.cert_checkM Curve3Pool.cert_jumpsOkM hcode hfork ⟨Curve3Pool.t_0000_c0, rfl, hr⟩
  exact ⟨D, Lift.exec_withGas_of_frame exD, hDg, hend⟩

/-! ## The words -/

/-- The output's, the fee's and the cut's words read back. -/
theorem swap_word_reads {w : Jaune.State} {i j : Fin 3} {xj fee af : B256} {net v y d2 f dy admin : Nat}
    (g : SwapWords w i j net y d2 f dy admin) (hx : xj.toNat = scaled w j) (hv : (Nat.toB256 v).toNat = y)
    (hfee : fee.toNat = word w pool feeSlot) (haf : af.toNat = word w pool adminFeeSlot)
    (hd : d2 < 2 ^ 190) (hfb : word w pool feeSlot ≤ feeDen) (hab : word w pool adminFeeSlot ≤ feeDen) :
    (exDyFee xj (Nat.toB256 v) fee).toNat = f ∧ (exDyOut xj (Nat.toB256 v) fee (exRate j.val)).toNat = dy ∧
      (exAdm (exDyFee xj (Nat.toB256 v) fee) af (exRate j.val)).toNat = admin := by
  have hgot := g.got
  have hden : feeDen = 10000000000 := rfl
  have hprec : precision = 1000000000000000000 := rfl
  have hR : exR0.toNat = precision := by decide
  have hD : exFeeDen.toNat = feeDen := by decide
  have h1 : (Bytes.toB256 [1]).toNat = 1 := by decide
  have hs1 : (xj - Nat.toB256 v).toNat = d2 + 1 := by
    rw [sub_nat (by rw [hx, hv]; omega), hx, hv]
    omega
  have hs2 : (exDy0 xj (Nat.toB256 v)).toNat = d2 := by
    unfold exDy0
    rw [sub_nat (by rw [hs1, h1]; omega), hs1, h1]
    omega
  have hmf : (exDy0 xj (Nat.toB256 v)).toNat * fee.toNat < 2 ^ 256 := by
    rw [hs2, hfee]
    calc d2 * word w pool feeSlot ≤ 2 ^ 190 * 2 ^ 40 := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 256 := by decide
  have hF : (exDyFee xj (Nat.toB256 v) fee).toNat = f := by
    unfold exDyFee
    rw [Lift.rlOut_toNat hmf (by decide), hs2, hfee, hD, g.fee]
  have hle := g.feeLe
  have hsO : (exDy0 xj (Nat.toB256 v) - exDyFee xj (Nat.toB256 v) fee).toNat = d2 - f := by
    rw [sub_nat (by rw [hs2, hF]; exact hle), hs2, hF]
  have hmo : (exDy0 xj (Nat.toB256 v) - exDyFee xj (Nat.toB256 v) fee).toNat * exR0.toNat < 2 ^ 256 := by
    rw [hsO, hR, hprec]
    calc (d2 - f) * 1000000000000000000 ≤ 2 ^ 190 * 2 ^ 60 := Nat.mul_le_mul (by omega) (by decide)
      _ < 2 ^ 256 := by decide
  have hma : (exDyFee xj (Nat.toB256 v) fee).toNat * af.toNat < 2 ^ 256 := by
    rw [hF, haf]
    calc f * word w pool adminFeeSlot ≤ 2 ^ 190 * 2 ^ 40 := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 256 := by decide
  have hq : (exAdm0 (exDyFee xj (Nat.toB256 v) fee) af).toNat = f * word w pool adminFeeSlot / feeDen := by
    unfold exAdm0
    rw [Lift.rlOut_toNat hma (by decide), hF, haf, hD]
  have hql : f * word w pool adminFeeSlot / feeDen ≤ f :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hab)
  have hmq : (exAdm0 (exDyFee xj (Nat.toB256 v) fee) af).toNat * exR0.toNat < 2 ^ 256 := by
    rw [hq, hR, hprec]
    calc f * word w pool adminFeeSlot / feeDen * 1000000000000000000 ≤ 2 ^ 190 * 2 ^ 60 := Nat.mul_le_mul (by omega) (by decide)
      _ < 2 ^ 256 := by decide
  refine ⟨hF, ?_, ?_⟩
  · unfold exDyOut
    rw [Lift.rlOut_toNat hmo (exRate_ne), hsO, hR, ex_rate_nat, g.out]
  · unfold exAdm
    rw [Lift.rlOut_toNat hmq (exRate_ne), hq, hR, ex_rate_nat, g.cut]

/-! ## USDT's ledger after its pull -/

/-- The pool's word after USDT's pull, and that the pull leaves the deprecation word. -/
theorem usdt_pulled_get {w : Jaune.State} {E : Adr} {v : Nat} (hap : SwapApart w E) (hv : v < 2 ^ 256) (hfl : usdtFee w v ≤ v) (hf : v * word w usdt 3 < 2 ^ 256)
    (hcr : word w usdt (Usdt.balSlot pool) + (v - usdtFee w v) < 2 ^ 255) :
    ((pulledK 2 (w.getStor usdt) E pool (Nat.toB256 v)).get (Usdt.balSlot pool)).toNat = word w usdt (Usdt.balSlot pool) + (v - usdtFee w v) ∧
      (pulledK 2 (w.getStor usdt) E pool (Nat.toB256 v)).get 10 = (w.getStor usdt).get 10 := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  have hfe := feeOf_nat hv hf
  have hsub : (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)).toNat = v - usdtFee w v := by
    rw [sub_nat (by rw [hs, hfe]; exact hfl), hs, hfe]
  obtain ⟨a1, a2⟩ := hap.allow 2
  have a1' : Usdt.allowSlot E pool ≠ Usdt.balSlot E := a1
  have a2' : Usdt.allowSlot E pool ≠ Usdt.balSlot pool := a2
  have hAu := hap.allowUsdt
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hAu
  obtain ⟨a0, -, -, a10, -, aO⟩ := hAu
  have hEp : Usdt.balSlot E ≠ Usdt.balSlot pool := hap.poolEntry 2
  have hE1 := hap.usdtE.1
  have hO1 := hap.usdtOwner.1
  simp only [usdtGateSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at hE1 hO1
  have hS : ∀ k, k ≠ Usdt.allowSlot E pool → (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)).get k = (w.getStor usdt).get k := fun k hk => by
    unfold Usdt.spendStor
    split
    · rfl
    · exact Stor.get_set_ne _ (Ne.symm hk) _
  have hE0 : Usdt.balSlot E ≠ 0 := fun e => hE1.2.2.2.2 (by
    show Usdt.balSlot E = _
    rw [e]; decide)
  have hE10 : Usdt.balSlot E ≠ 10 := fun e => hE1.2.2.1 (by
    show Usdt.balSlot E = _
    rw [e]; decide)
  have hp0 : Usdt.balSlot pool ≠ 0 := usdt_pool_ne_zero
  have hp10 : Usdt.balSlot pool ≠ 10 := by decide +kernel
  have ha0 : (0 : B256) ≠ Usdt.allowSlot E pool := fun e => a0 (show Usdt.allowSlot E pool = _ by rw [← e]; decide)
  have ha10 : (10 : B256) ≠ Usdt.allowSlot E pool := fun e => a10 (show Usdt.allowSlot E pool = _ by rw [← e]; decide)
  have hPO : Usdt.balSlot pool ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := Ne.symm hap.usdtOwner.2
  have hO10 : Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) ≠ 10 := fun e => hO1.2.2.1 (by
    show Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) = _
    rw [e]; decide)
  obtain ⟨σ', hσ'⟩ : ∃ σ', σ' = Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v) := ⟨_, rfl⟩
  have hown : Usdt.ownerOf (Usdt.credit (Usdt.debit σ' E (Nat.toB256 v)) pool (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))) = Usdt.ownerOf (w.getStor usdt) := by
    unfold Usdt.ownerOf Usdt.credit Usdt.debit
    rw [Stor.get_set_ne _ hp0, Stor.get_set_ne _ hE0, hσ', hS _ ha0]
  show ((Usdt.moveStor (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)) E pool (Nat.toB256 v) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))).get (Usdt.balSlot pool)).toNat = _ ∧
    (Usdt.moveStor (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)) E pool (Nat.toB256 v) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))).get 10 = _
  rw [← hσ']
  have hpv : σ'.get (Usdt.balSlot pool) = (w.getStor usdt).get (Usdt.balSlot pool) := by rw [hσ', hS _ (Ne.symm a2')]
  have h10v : σ'.get 10 = (w.getStor usdt).get 10 := by rw [hσ', hS _ ha10]
  have hcredit : ((Usdt.credit (Usdt.debit σ' E (Nat.toB256 v)) pool (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))).get (Usdt.balSlot pool)).toNat =
      word w usdt (Usdt.balSlot pool) + (v - usdtFee w v) := by
    unfold Usdt.credit Usdt.debit
    rw [Stor.get_set_self, Stor.get_set_ne _ hEp, hpv, toNat_add_of (by rw [hsub]; show word w usdt (Usdt.balSlot pool) + _ < _; omega), hsub]
    rfl
  have h10c : (Usdt.credit (Usdt.debit σ' E (Nat.toB256 v)) pool (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))).get 10 = (w.getStor usdt).get 10 := by
    unfold Usdt.credit Usdt.debit
    rw [Stor.get_set_ne _ hp10, Stor.get_set_ne _ hE10, h10v]
  unfold Usdt.moveStor
  split
  · exact ⟨hcredit, h10c⟩
  · rw [hown]
    constructor
    · unfold Usdt.credit at hcredit ⊢
      rw [Stor.get_set_ne _ (Ne.symm hPO)]
      exact hcredit
    · unfold Usdt.credit
      rw [Stor.get_set_ne _ hO10]
      exact h10c

/-! ## The model's words -/

/-- The words the model's `exchange` comes to, and what they read back as. -/
structure SwapModel (e0 : Sevm) (σ : Stor) (s0 : Curve3Pool.State) (w : Jaune.State) (i j : Fin 3) (dx dy admin : Nat) (x0 x1 x2 B1 B2 : B256)
    (amp v : Nat) (hi3 : (exI e0).toNat < 3) (hj3 : (exJ e0).toNat < 3) : Prop where
  hX : xpChk ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩
  hmx : exCred e0 B1 B2 * exRate (exI e0).toNat / exCred e0 B1 B2 =
      exRate (exI e0).toNat ∨ exCred e0 B1 B2 = 0
  hax : ¬ exW3 x0 x1 x2 (exI e0).toNat + exCred e0 B1 B2 * exRate (exI e0).toNat / exR0 <
      exW3 x0 x1 x2 (exI e0).toNat
  hA : aChk s0 e0.benvStat.time.toNat = some amp
  hres : getYChk amp ⟨(exI e0).toNat, hi3⟩ ⟨(exJ e0).toNat, hj3⟩
      (exW3 x0 x1 x2 (exI e0).toNat + exCred e0 B1 B2 * exRate (exI e0).toNat / exR0).toNat
      (V3.mk x0.toNat x1.toNat x2.toNat).get = some v
  hy1 : ¬ exW3 x0 x1 x2 (exJ e0).toNat < Nat.toB256 v
  hy2 : ¬ exW3 x0 x1 x2 (exJ e0).toNat - Nat.toB256 v < Bytes.toB256 [1]
  hmf : exDy0 (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) *
        σ.get feeSlot /
        exDy0 (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) =
        σ.get feeSlot ∨
      exDy0 (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) = 0
  hsf : ¬ exDy0 (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) <
      exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
        (σ.get feeSlot)
  hmo : (exDy0 (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
          (σ.get feeSlot)) * exR0 /
        (exDy0 (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) -
          exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
            (σ.get feeSlot)) = exR0 ∨
      exDy0 (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
          (σ.get feeSlot) = 0
  hmin : ¬ exDyOut (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
      (σ.get feeSlot) (exRate (exJ e0).toNat) < exMinDy e0
  hma : exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
        (σ.get feeSlot) *
        σ.get adminFeeSlot /
        exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
          (σ.get feeSlot) =
        σ.get adminFeeSlot ∨
      exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
        (σ.get feeSlot) = 0
  hmap : exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
        (σ.get feeSlot))
        (σ.get adminFeeSlot) * exR0 /
        exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
          (σ.get feeSlot))
          (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
        (σ.get feeSlot))
        (σ.get adminFeeSlot) = 0
  hbi : ¬ exBal σ ⟨(exI e0).toNat, hi3⟩ + exCred e0 B1 B2 <
      exBal σ ⟨(exI e0).toNat, hi3⟩
  hbj1 : ¬ exBal σ ⟨(exJ e0).toNat, hj3⟩ <
      exDyOut (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
        (σ.get feeSlot) (exRate (exJ e0).toNat)
  hbj2 : ¬ exBal σ ⟨(exJ e0).toNat, hj3⟩ -
        exDyOut (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
          (σ.get feeSlot) (exRate (exJ e0).toNat) <
      exAdm (exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v)
        (σ.get feeSlot))
        (σ.get adminFeeSlot) (exRate (exJ e0).toNat)
  sub : exI e0 = 2 → ¬ B2 < B1
  xN : ∀ k : Fin 3, (exW3 x0 x1 x2 k.val).toNat = scaled w k
  Dn : (exCred e0 B1 B2).toNat = netOf w i dx
  xvN : (exW3 x0 x1 x2 (exI e0).toNat + exCred e0 B1 B2 * exRate (exI e0).toNat / exR0).toNat = scaled w i + netOf w i dx * rates.get i / precision
  On : (exDyOut (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ e0).toNat)).toNat = dy
  An : (exAdm (exDyFee (exW3 x0 x1 x2 (exJ e0).toNat) (Nat.toB256 v) (σ.get feeSlot)) (σ.get adminFeeSlot) (exRate (exJ e0).toNat)).toNat = admin
  room : dy + admin + 1 ≤ recorded w j

/-- **The model's `exchange` as the frame's words.** -/
theorem swap_model {e0 : Sevm} {σ : Stor} {w : Jaune.State} {s0 : Curve3Pool.State} {i j : Fin 3} {dx dy minDy amp DD : Nat} {B1 B2 : B256}
    (hS : σ = w.getStor pool) (hab : Abstracts σ s0) (hk : s0.isKilled = false) (hij : i ≠ j)
    (hiw : exI e0 = Nat.toB256 i.val) (hjw : exJ e0 = Nat.toB256 j.val) (hdxw : exDx e0 = Nat.toB256 dx) (hmdw : exMinDy e0 = Nat.toB256 minDy)
    (hdxN : dx < 2 ^ 256) (hmdN : minDy < 2 ^ 256)
    (hnet : pullIn (exEnv e0 i j (exBalOpt i B1) (exBalOpt i B2)) i dx = some (netOf w i dx))
    (hinv : invariant w amp = some DD) (hA : ampAt w e0.benvStat.time.toNat = some amp)
    (hfee : word w pool feeSlot ≤ feeDen) (haf : word w pool adminFeeSlot ≤ feeDen)
    (hq : swapOut w e0.benvStat.time.toNat i j dx = some dy) (hmin : minDy ≤ dy) (hfit : scaled w j < 2 ^ 190)
    (hbi : recorded w i + netOf w i dx < 2 ^ 256) :
    ∃ x0 x1 x2 v admin hi3 hj3, swapAdmin w e0.benvStat.time.toNat i j dx = some admin ∧
      SwapModel e0 σ s0 w i j dx dy admin x0 x1 x2 B1 B2 amp v hi3 hj3 := by
  subst hS
  obtain ⟨o, admin, y, d2, f, hex, hamt, hadm, hy, g⟩ := exchange_accepts (e := exEnv e0 i j (exBalOpt i B1) (exBalOpt i B2)) (minDy := minDy) hab hk hij hnet hinv hA hfee haf hq hmin hfit hbi (by
    simp only [exEnv, decide_true])
  have hiN : i.val = (exI e0).toNat := by rw [hiw, B256.toNat_toB256_of_lt (by have := i.isLt; omega)]
  have hjN : j.val = (exJ e0).toNat := by rw [hjw, B256.toNat_toB256_of_lt (by have := j.isLt; omega)]
  have hex' : exchange s0 (exEnv e0 i j (exBalOpt i B1) (exBalOpt i B2)) i j (exDx e0).toNat (exMinDy e0).toNat = some o := by
    rw [hdxw, hmdw, B256.toNat_toB256_of_lt hdxN, B256.toNat_toB256_of_lt hmdN]
    exact hex
  obtain ⟨x0, x1, x2, amp', v, hi3, hj3, -, hX, hsub, hmx, hax, hA', hres, hy1, hy2, hmf, hsf, hmo, hmin', hma, hmap, hbi', hbj1, hbj2, hpa, -, -, hpl, -⟩ :=
    ex_words hab hiN hjN hex'
  obtain rfl : amp = amp' := Option.some.inj ((by rw [← ampAt_of_abstracts hab]; exact hA : aChk s0 e0.benvStat.time.toNat = some amp).symm.trans hA')
  have hxg : (V3.mk x0.toNat x1.toNat x2.toNat).get = scaled w := Curve3Pool.xpChk_some (b := books w) hX
  have xN : ∀ k : Fin 3, (exW3 x0 x1 x2 k.val).toNat = scaled w k := fun k => by
    rw [ex_w3_nat, hxg]
  have Dn : (exCred e0 B1 B2).toNat = netOf w i dx := by
    rw [hdxw, B256.toNat_toB256_of_lt hdxN, hnet] at hpl
    exact (Option.some.inj hpl).symm
  obtain ⟨ampq, xq, yq, d1q, dq, pq, fq, hamq, hxq, hpq, hyq, -, -, -⟩ := swapOut_parts hq
  have hmL : netOf w i dx * rates.get i < 2 ^ 256 := Blanc.StableSwapNewton.chkMul_some_lt hxq
  have hxe : xq = netOf w i dx * rates.get i := Blanc.StableSwapNewton.chkMul_some hxq
  have hpe : pq = netOf w i dx * rates.get i / precision := by rw [(Blanc.StableSwapNewton.chkDiv_some hpq).1, hxe]
  have haL : scaled w i + netOf w i dx * rates.get i / precision < 2 ^ 256 := by
    have := Blanc.StableSwapNewton.chkAdd_some_lt hyq
    rw [hpe] at this
    exact this
  have hxIn : (exW3 x0 x1 x2 (exI e0).toNat).toNat = scaled w i := by rw [← hiN]; exact xN i
  have hMn : (exCred e0 B1 B2 * exRate (exI e0).toNat / exR0).toNat = netOf w i dx * rates.get i / precision := by
    rw [← hiN, Lift.rlOut_toNat (by rw [Dn, ex_rate_nat]; exact hmL) (by decide), Dn, ex_rate_nat]
    rfl
  have xvN : (exW3 x0 x1 x2 (exI e0).toNat + exCred e0 B1 B2 * exRate (exI e0).toNat / exR0).toNat =
      scaled w i + netOf w i dx * rates.get i / precision := by
    rw [toNat_add_of (by rw [hxIn, hMn]; exact haL), hxIn, hMn]
  have hres' : getYChk amp i j (scaled w i + netOf w i dx * rates.get i / precision) (scaled w) = some v := by
    have e1 : (⟨(exI e0).toNat, hi3⟩ : Fin 3) = i := Fin.ext hiN.symm
    have e2 : (⟨(exJ e0).toNat, hj3⟩ : Fin 3) = j := Fin.ext hjN.symm
    rw [e1, e2, xvN, hxg] at hres
    exact hres
  obtain rfl : v = y := Option.some.inj (hres'.symm.trans hy)
  have hgot := g.got
  have hvN : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt (by omega)
  have hd190 : d2 < 2 ^ 190 := by omega
  obtain ⟨-, r2, r3⟩ := swap_word_reads (xj := exW3 x0 x1 x2 j.val) (fee := (w.getStor pool).get feeSlot) (af := (w.getStor pool).get adminFeeSlot) g (xN j) hvN rfl rfl hd190 hfee haf
  rw [hjN] at r2 r3
  exact ⟨x0, x1, x2, v, admin, hi3, hj3, hadm,
    { hX := hX, hmx := hmx, hax := hax, hA := hA', hres := hres, hy1 := hy1, hy2 := hy2, hmf := hmf, hsf := hsf, hmo := hmo, hmin := hmin', hma := hma, hmap := hmap,
      hbi := hbi', hbj1 := hbj1, hbj2 := hbj2, sub := hsub, xN := xN, Dn := Dn, xvN := xvN, On := r2, An := r3, room := g.room }⟩

/-! ## The debits -/

theorem swap_debit_bounds (e : Sevm) (d : Devm) (i j : Fin 3) :
    (∀ b S M, (swapCalls e d i j).balD1 b S M ≤ 200000) ∧ (∀ b S M, (swapCalls e d i j).balD2 b S M ≤ 200000) ∧
      (∀ b S M, (swapCalls e d i j).pullD b S M ≤ 200000) ∧ (∀ b S M, (swapCalls e d i j).pushD b S M ≤ 200000) := by
  have hb1 : ∀ b S M, (swapCalls e d i j).balD1 b S M ≤ 8047 := fun b S M => Blanc.Composition.Curve3PoolUsdt.usdt_balDebit_le (by decide) (by decide) b S M
  have hb2 : ∀ b S M, (swapCalls e d i j).balD2 b S M ≤ 8047 := fun b S M => Blanc.Composition.Curve3PoolUsdt.usdt_balDebit_le (by decide) (by decide) b S M
  refine ⟨fun b S M => Nat.le_trans (hb1 b S M) (by decide), fun b S M => Nat.le_trans (hb2 b S M) (by decide), fun b S M => ?_, fun b S M => ?_⟩
  · show Blanc.Composition.Curve3Pool3CrvLiteralWitness.swapPullD e _ i b S M ≤ _
    obtain ⟨t, ht⟩ : ∃ t, t = (d.getStor e.currentTarget).get (coinSlot i) := ⟨_, rfl⟩
    rw [← ht]
    have ha : Blanc.Composition.Curve3PoolCalleeLive.acc (b.withGasLeft 0) t ≤ 2600 := Blanc.Composition.Curve3PoolCalleeLive.acc_le
    have he : Blanc.Composition.Curve3PoolCalleeLive.ext (b.withGasLeft 0) S M 0x600 0x64 0x6c0 0x20 ≤ 416 := Blanc.Composition.Curve3PoolCalleeLive.ext_le (by decide) (by decide)
    obtain ⟨c, hc⟩ : ∃ c, c = Blanc.Composition.Curve3PoolCalleeLive.callMsg0 e (b.withGasLeft 0) S M 0 t 0x600 0x64 0x6c0 0x20 := ⟨_, rfl⟩
    match i with
    | 0 =>
      show Blanc.Composition.Curve3PoolCoinExactKit.coinDebit Dai.pullG e t 0x600 0x64 0x6c0 b S M ≤ _
      unfold Blanc.Composition.Curve3PoolCoinExactKit.coinDebit
      rw [← hc]
      have := Dai.pullG_le (initSevm c) (initDevm c)
      omega
    | 1 =>
      show Blanc.Composition.Curve3PoolCoinExactKit.coinDebit Blanc.Composition.UsdcLive.pullG e t 0x600 0x64 0x6c0 b S M ≤ _
      unfold Blanc.Composition.Curve3PoolCoinExactKit.coinDebit
      rw [← hc]
      have hl : (initSevm c).data.length ≤ 100 := by rw [hc, Blanc.Composition.Curve3PoolCalleeLive.callMsg0_data, mem_read_len]; decide
      have := Blanc.Composition.UsdcLive.proxyG_le (w := 1) (impl := Blanc.Composition.UsdcLive.implPullG) (Cu := 102000) (s' := initSevm c) (p := initDevm c) hl (by
        have h := Blanc.Composition.UsdcLive.pullW_le (sevm := initSevm (Blanc.Composition.UsdcLive.dMsg (initSevm c) (initDevm c) 0)) (b := initDevm (Blanc.Composition.UsdcLive.dMsg (initSevm c) (initDevm c) 0))
        rwa [Blanc.Composition.UsdcLive.pullW_eq] at h)
      show _ + _ + Blanc.Composition.UsdcLive.proxyG 1 Blanc.Composition.UsdcLive.implPullG (initSevm c) (initDevm c) ≤ _
      omega
    | 2 =>
      show Blanc.Composition.Curve3PoolCoinExactKit.coinDebit Usdt.pullG e t 0x600 0x64 0x6c0 b S M ≤ _
      unfold Blanc.Composition.Curve3PoolCoinExactKit.coinDebit
      rw [← hc]
      have h := Usdt.pullW_le (sevm := initSevm c) (b := initDevm c)
      rw [Usdt.pullW_eq] at h
      omega
  · show Blanc.Composition.Curve3Pool3CrvLiteralWitness.swapPushD e _ j b S M ≤ _
    obtain ⟨t, ht⟩ : ∃ t, t = (d.getStor e.currentTarget).get (coinSlot j) := ⟨_, rfl⟩
    rw [← ht]
    have ha : Blanc.Composition.Curve3PoolCalleeLive.acc (b.withGasLeft 0) t ≤ 2600 := Blanc.Composition.Curve3PoolCalleeLive.acc_le
    have he : Blanc.Composition.Curve3PoolCalleeLive.ext (b.withGasLeft 0) S M 0xb60 0x44 0xc00 0x20 ≤ 416 := Blanc.Composition.Curve3PoolCalleeLive.ext_le (by decide) (by decide)
    obtain ⟨c, hc⟩ : ∃ c, c = Blanc.Composition.Curve3PoolCalleeLive.callMsg0 e (b.withGasLeft 0) S M 0 t 0xb60 0x44 0xc00 0x20 := ⟨_, rfl⟩
    match j with
    | 0 =>
      show Blanc.Composition.Curve3PoolCoinExactKit.coinDebit Dai.xferG e t 0xb60 0x44 0xc00 b S M ≤ _
      unfold Blanc.Composition.Curve3PoolCoinExactKit.coinDebit
      rw [← hc]
      have := dai_xferG_le (initSevm c) (initDevm c)
      omega
    | 1 =>
      show Blanc.Composition.Curve3PoolCoinExactKit.coinDebit Blanc.Composition.UsdcLive.xferG e t 0xb60 0x44 0xc00 b S M ≤ _
      unfold Blanc.Composition.Curve3PoolCoinExactKit.coinDebit
      rw [← hc]
      have := proxy_xferG_le (e := initSevm c) (d := initDevm c) (by rw [hc, Blanc.Composition.Curve3PoolCalleeLive.callMsg0_data, mem_read_len]; decide)
      omega
    | 2 =>
      show Blanc.Composition.Curve3PoolCoinExactKit.coinDebit Usdt.xferG e t 0xb60 0x44 0xc00 b S M ≤ _
      unfold Blanc.Composition.Curve3PoolCoinExactKit.coinDebit
      rw [← hc]
      have := usdt_xferG_le (initSevm c) (initDevm c)
      omega

/-! ## The message -/

theorem pullIn_other {e0 : Sevm} {i j : Fin 3} {bp bq : Option Nat} (hi : i ≠ feeIndex) (dx : Nat) : pullIn (exEnv e0 i j bp bq) i dx = some dx := by
  unfold pullIn
  rw [ite_eq_right hi]
  simp only [exEnv, decide_true, req]
  rfl

theorem pullIn_two {e0 : Sevm} {j : Fin 3} {a b : Nat} (dx : Nat) : pullIn (exEnv e0 2 j (some a) (some b)) 2 dx = Blanc.StableSwapNewton.chkSub b a := by
  unfold pullIn
  rw [ite_eq_left (by decide : (2 : Fin 3) = feeIndex)]
  simp only [exEnv, decide_true, req, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]

theorem swapOut_lt {w : Jaune.State} {t : Nat} {i j : Fin 3} {dx dy : Nat} (hq : swapOut w t i j dx = some dy) (hfit : scaled w j < 2 ^ 190) : dy < 2 ^ 190 := by
  obtain ⟨-, -, -, d1, d, -, f, -, -, -, -, -, hd, d2, -, hd2, -, -, hout, -⟩ := swapOut_parts hq
  obtain ⟨ed, -⟩ := Blanc.StableSwapNewton.chkSub_some hd
  obtain ⟨ed2, -⟩ := Blanc.StableSwapNewton.chkSub_some hd2
  rw [hout, div_rate]
  have := Nat.div_le_self (d2 - f) (Curve3Pool.precMul.get j)
  omega

theorem held_le_word (w : Jaune.State) (a : Adr) (k : Fin 3) : coinHeld w a k ≤ word w (coinAt k) (coinEntry a k) := by
  unfold coinHeld
  split
  · rename_i h
    obtain ⟨rfl, -⟩ := h
    exact Nat.mod_le _ _
  · exact Nat.le_refl _

theorem getY_ann {amp x v : Nat} {i j : Fin 3} {xp : Fin 3 → Nat} (h : getYChk amp i j x xp = some v) : Blanc.StableSwapNewton.chkMul amp 3 = some (amp * 3) := by
  unfold getYChk at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨-, -, ann, hann, -⟩ := h
    rw [hann, Blanc.StableSwapNewton.chkMul_some hann]

/-- The parties' storage at an asked message's entry, and its coin stand. -/
theorem asked_stand {msg : Msg} {w : Jaune.State} {E : Adr} {data : Bytes} (e : Asked msg w E data) (hap : CoinsApart w E) (F : Nat) :
    CoinStand {initSevm msg with gas := F} (initDevm msg) w E := by
  have hopen := e.coinsOpen
  have hI : usdcImplOf w = Usdc.usdcImpl := by
    unfold usdcImplOf
    rw [show (w.getStor usdc).get Usdc.implSlot = Usdc.usdcImpl.toB256 from hopen.usdcV22.1, toAdr_toB256]
  exact
    { fork := e.entry.plain.2.2.2
      target := e.entry.named.1
      caller := e.entry.named.2.1
      keysCold := fun k hk => by
        have h0 : (initDevm msg).accessedStorageKeys.isEmpty = true := e.entry.cold.1
        exact absurd (Std.HashSet.isEmpty_eq_false_iff_exists_mem.2 ⟨k, hk⟩) (by simpa only [Bool.not_eq_false] using h0)
      clean := ⟨e.entry.fresh.1, e.entry.fresh.2, rfl⟩
      stor := fun x hx => by
        have hm : x ∈ parties w := by
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [parties, List.mem_cons, true_or, or_true]
        have h := e.entry.world x hm
        exact ⟨congrArg Acct.stor h.1, congrArg Acct.stor h.2⟩
      warm := fun x hx => by
        refine e.entry.cold.2 x ?_
        simp only [parties, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, hI]
        exact hx
      apart := hap
      open' := hopen }

/-- The chain's standing at any static gas. -/
theorem swap_chain_of {msg : Msg} {w : Jaune.State} {E : Adr} {i j : Fin 3} {dx dy admin amp v DD : Nat} {x0 x1 x2 B1 B2 F0 O A0 : B256} {s : Curve3Pool.State} {data : Bytes} {hi3 hj3}
    (e : Asked msg w E data) (hck0 : Checkpoint (w.getStor pool) s) (hco : ∀ k, coinOf (initSevm msg) (initDevm msg) k = coinAt k)
    (hap : SwapApart w E) (hij : i ≠ j) (hiw : exI (initSevm msg) = Nat.toB256 i.val) (hjw : exJ (initSevm msg) = Nat.toB256 j.val) (hdxw : exDx (initSevm msg) = Nat.toB256 dx)
    (hE0 : E ≠ 0) (hinv : invariant w amp = some DD)
    (M : SwapModel (initSevm msg) ((initDevm msg).getStor (initSevm msg).currentTarget) s w i j dx dy admin x0 x1 x2 B1 B2 amp v hi3 hj3)
    (hσ : (initDevm msg).getStor (initSevm msg).currentTarget = w.getStor pool)
    (hO : O = exDyOut (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) ((w.getStor pool).get feeSlot) (exRate (exJ (initSevm msg)).toNat))
    (hF0 : F0 = exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) ((w.getStor pool).get feeSlot))
    (hA0 : A0 = exAdm F0 ((w.getStor pool).get adminFeeSlot) (exRate (exJ (initSevm msg)).toNat))
    (hOn : O.toNat = dy) (hAn : A0.toNat = admin)
    (hle : dx ≤ coinHeld w E i) (hal : dx ≤ allowanceOf w E i) (hcrP : CreditFits w pool i (netOf w i dx)) (hcrE : CreditFits w E j (netOf w j dy))
    (hfeeI : UsdtFeeFits w dx) (hfeeJ : UsdtFeeFits w dy) (hdx0 : 0 < dx) (hdy0 : 0 < dy) (hbi : recorded w i + netOf w i dx < 2 ^ 256) (hcov : recorded w j ≤ coinHeld w pool j) :
    ∀ F, SwapChain {initSevm msg with gas := F} (initDevm msg) w E i j dx dy admin x0 x1 x2 B1 B2 F0 O A0 amp v
      (scaled w i + netOf w i dx * rates.get i / precision) DD := by
  have hiN : i.val = (exI (initSevm msg)).toNat := by rw [hiw, B256.toNat_toB256_of_lt (by have := i.isLt; omega)]
  have hjN : j.val = (exJ (initSevm msg)).toNat := by rw [hjw, B256.toNat_toB256_of_lt (by have := j.isLt; omega)]
  have hOw : O = Nat.toB256 dy := by rw [← hOn, toB256_toNat]
  have hL : ∀ k, k ≠ lockW → (lockedStor w).get k = (w.getStor pool).get k := fun k hk => Stor.get_set_ne _ (Ne.symm hk) _
  have hrec : ∀ k : Fin 3, ((lockedStor w).get (balancesBase + Nat.toB256 k.val)).toNat = recorded w k := fun k => by
    rw [hL _ (bal_ne_lockW k)]; rfl
  have hroom := M.room
  have hCoin : ∀ k : Fin 3, ((lockedStor w).get (coinsBase + Nat.toB256 k.val)).toAdr = coinAt k := fun k => by
    rw [← chain_coin k, ← hco k]
    show _ = (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot k)).toAdr
    rw [hσ]
  have hxK : ∀ k : Fin 3, (exW3 x0 x1 x2 k.val).toNat = scaled w k := M.xN
  have hVs : (V3.mk (scaled w 0) (scaled w 1) (scaled w 2)).get = scaled w := by
    funext k
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have hDk : Blanc.StableSwapNewton.getDChk (V3.mk (scaled w 0) (scaled w 1) (scaled w 2)).get amp 1 = some DD := by
    unfold invariant Curve3Pool.getDMem at hinv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hinv
    obtain ⟨xp, hxp, hd⟩ := hinv
    have hxg : xp.get = scaled w := Curve3Pool.xpChk_some hxp
    rw [hVs, ← hxg]
    exact hd
  have hAnn := getY_ann M.hres
  intro F
  exact
    { back :=
        { stand := asked_stand e hap.toCoinsApart F
          static := e.entry.plain.2.1
          iw := hiw
          jw := hjw
          differ := hij
          named := hE0
          coinJ := hCoin j
          lock := hck0.unlocked
          credit := by
            have h := M.Dn
            rw [hrec i]
            show (exCred (initSevm msg) B1 B2).toNat + _ < _
            rw [h]
            omega
          below := by rw [hrec j, hOn, hAn]; omega
          out := hOw
          pays := ⟨by omega, hcrE, fun _ => hfeeJ⟩ }
      apart := hap
      coinI := hCoin i
      dxw := hdxw
      hF := hF0.symm
      hO := hO.symm
      hA := hA0.symm
      Dn := M.Dn
      On := hOn
      An := hAn
      holds := ⟨hle, hal⟩
      creditP := hcrP
      feeI := fun _ => hfeeI
      moved := ⟨hdx0, hdy0⟩
      hY := fun b => by
        have e0 : (exW3 x0 x1 x2 0).toNat = scaled w 0 := hxK 0
        have e1 : (exW3 x0 x1 x2 1).toNat = scaled w 1 := hxK 1
        have e2 : (exW3 x0 x1 x2 2).toNat = scaled w 2 := hxK 2
        have eI : (exI {initSevm msg with gas := F}).toNat = i.val := hiN.symm
        have eJ : (exJ {initSevm msg with gas := F}).toNat = j.val := hjN.symm
        unfold costGetY newtonGas
        rw [e0, e1, e2, hDk, hAnn, eI, eJ]
        have hxe : (exXw {initSevm msg with gas := F} (exW3 x0 x1 x2) (exCred {initSevm msg with gas := F} B1 B2)).toNat = scaled w i + netOf w i dx * rates.get i / precision := M.xvN
        rw [hxe] }

/-- The fee coin's two reads around the pull, and what the model credits. -/
theorem swap_B {msg : Msg} {w : Jaune.State} {E : Adr} {i j : Fin 3} {dx : Nat} {B1 B2 : B256}
    (hB1 : B1 = swapB1 (initSevm msg) (initDevm msg) i) (hB2 : B2 = swapB2 (initSevm msg) (initDevm msg) i)
    (hcoi : coinOf (initSevm msg) (initDevm msg) i = coinAt i) (hcoinS : (initDevm msg).getStor (coinAt i) = w.getStor (coinAt i))
    (hTt : (initSevm msg).currentTarget = pool) (hTc : (initSevm msg).caller = E) (hdxw : exDx (initSevm msg) = Nat.toB256 dx)
    (mk : ExitMarked w) (hap : SwapApart w E) (hdxN : dx < 2 ^ 256) (hfeeI : UsdtFeeFits w dx) (hcrP : CreditFits w pool i (netOf w i dx)) :
    (i = 2 → B1.toNat = word w usdt (Usdt.balSlot pool) ∧ B2.toNat = word w usdt (Usdt.balSlot pool) + netOf w i dx ∧
      Usdt.NotDeprecated (pulledK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).caller (initSevm msg).currentTarget (exDx (initSevm msg)))) ∧
    pullIn (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i dx = some (netOf w i dx) := by
  have hBw : i = 2 → B1.toNat = word w usdt (Usdt.balSlot pool) ∧ B2.toNat = word w usdt (Usdt.balSlot pool) + netOf w i dx ∧
      Usdt.NotDeprecated (pulledK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).caller (initSevm msg).currentTarget (exDx (initSevm msg))) := by
    intro h2
    subst h2
    have hP := usdt_pulled_get (w := w) (E := E) (v := dx) hap hdxN hfeeI.2.2 hfeeI.1 hcrP
    have hEn : (initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2) = w.getStor usdt := by rw [hcoi]; exact hcoinS
    refine ⟨?_, ?_, ?_⟩
    · rw [hB1]
      show (((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2)).get (Usdt.balSlot (initSevm msg).currentTarget)).toNat = _
      rw [hEn, hTt]
      rfl
    · rw [hB2]
      show (((pulledK 2 ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2)) (initSevm msg).caller (initSevm msg).currentTarget (exDx (initSevm msg))).get (Usdt.balSlot (initSevm msg).currentTarget))).toNat = _
      rw [hEn, hTt, hTc, hdxw]
      exact hP.1
    · rw [hEn, hTt, hTc, hdxw]
      show Usdt.flag20 _ = 0
      rw [hP.2]
      exact mk.usdtLive
  have hnet : pullIn (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i dx = some (netOf w i dx) := by
    by_cases hi2 : i = 2
    · subst hi2
      obtain ⟨b1, b2, -⟩ := hBw rfl
      have e1 : exBalOpt 2 B1 = some B1.toNat := ite_eq_left (by decide)
      have e2 : exBalOpt 2 B2 = some B2.toNat := ite_eq_left (by decide)
      rw [e1, e2, pullIn_two, b1, b2]
      unfold Blanc.StableSwapNewton.chkSub
      rw [ite_eq_left (by omega)]
      congr 1
      omega
    · have hne : i ≠ feeIndex := hi2
      have hn : netOf w i dx = dx := by unfold netOf; rw [ite_eq_right hi2]
      rw [pullIn_other hne, hn]
  exact ⟨hBw, hnet⟩

theorem books_credit_lt {w : Jaune.State} {i : Fin 3} {n : Nat} (hc : recorded w i ≤ coinHeld w pool i) (hcr : CreditFits w pool i n) :
    recorded w i + n < 2 ^ 256 := by
  have h1 := held_le_word w pool i
  have h2 : word w (coinAt i) (coinEntry pool i) + n < 2 ^ 255 := hcr
  omega

theorem dy_le_held {w : Jaune.State} {j : Fin 3} {dy admin : Nat} (h : dy + admin + 1 ≤ recorded w j) (hc : recorded w j ≤ coinHeld w pool j) : dy ≤ coinHeld w pool j := by
  omega

theorem swapCalls_static (e : Sevm) (F : Nat) {d : Devm} {i j : Fin 3} : swapCalls {e with gas := F} d i j = swapCalls e d i j := rfl

/-- `SwapChain.eval` with the calls and the cost at no particular static gas. -/
theorem SwapChain.evalAt {e : Sevm} {F : Nat} {d : Devm} {w : Jaune.State} {E : Adr} {i j : Fin 3} {dx dy admin amp v xv DD : Nat} {x0 x1 x2 B1 B2 F0 O A0 : B256} {D' : Devm}
    (c : SwapChain {e with gas := F} d w E i j dx dy admin x0 x1 x2 B1 B2 F0 O A0 amp v xv DD)
    (he : ExFrameEnd {e with gas := F} d (swapCalls e d i j) x0 x1 x2 B1 B2 v D') :
    exExactCost e d (swapCalls e d i j) x0 x1 x2 B1 B2 amp v =
        swapFrameGas w E e.benvStat.time.toNat amp i j dx dy xv DD (decide (allowanceOf w E i = 2 ^ 256 - 1)) ∧
      ∃ T r, Mv T r d D' ∧ r = ((swapRefund w E i j dx dy (allowanceOf w E i) : Nat) : Int) ∧ SwapPaid w D'.state E i j dx dy admin := by
  have h := c.eval (D' := D') (by rw [swapCalls_static]; exact he)
  rw [swapCalls_static, exExactCost_withStaticGas] at h
  exact h

/-- **The run at any residual, from the chain's standing.** -/
theorem swap_finish {msg : Msg} {w : Jaune.State} {E : Adr} {i j : Fin 3} {dx dy admin amp v xv DD : Nat} {x0 x1 x2 B1 B2 F0 O A0 : B256} {data : Bytes}
    (e : Asked msg w E data)
    (hChain : ∀ F, SwapChain {initSevm msg with gas := F} (initDevm msg) w E i j dx dy admin x0 x1 x2 B1 B2 F0 O A0 amp v xv DD)
    (hrun : ∀ {R : Nat}, 2201 ≤ R → R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 amp v < 2 ^ 256 →
      ∃ post, exec (initEvm (msg.withGas (R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 amp v))) = .ok post ∧ post.gasLeft = R ∧
        ExFrameEnd {initSevm msg with gas := R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 amp v} (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 v post)
    (hlt : exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 amp v < 2 ^ 200) :
    ∀ R, callRoom ≤ R →
      R + swapFrameGas w E msg.benv.stat.time.toNat amp i j dx dy xv DD (decide (allowanceOf w E i = 2 ^ 256 - 1)) < 2 ^ 256 →
      ∃ post, exec (initEvm (msg.withGas (R + swapFrameGas w E msg.benv.stat.time.toNat amp i j dx dy xv DD
          (decide (allowanceOf w E i = 2 ^ 256 - 1))))) = .ok post ∧ post.error = none ∧ post.gasLeft = R ∧
        post.refundCounter = ((swapRefund w E i j dx dy (allowanceOf w E i) : Nat) : Int) ∧ post.accountsToDelete.toList = [] ∧
        SwapPaid w post.state E i j dx dy admin := by
  obtain ⟨post0, -, -, hend0⟩ := hrun (R := 2201) (Nat.le_refl _) (Nat.lt_trans (Nat.add_lt_add_left hlt 2201) (by decide))
  have hcost := ((hChain _).evalAt hend0).1
  have hcost' : exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 amp v =
      swapFrameGas w E msg.benv.stat.time.toNat amp i j dx dy xv DD (decide (allowanceOf w E i = 2 ^ 256 - 1)) := hcost
  intro R hR hG
  rw [← hcost'] at hG ⊢
  obtain ⟨post, hex, hg, hend⟩ := hrun (R := R) hR hG
  obtain ⟨-, T, r, mv, hr, paid⟩ := (hChain _).evalAt hend
  have hc0 : Clean (initDevm msg) := ⟨e.entry.fresh.1, e.entry.fresh.2, rfl⟩
  have hcp := mv.clean hc0
  refine ⟨post, hex, hcp.error, hg, ?_, List.eq_nil_iff_forall_not_mem.2 fun x h => hcp.del x (Std.HashSet.mem_toList.1 h), paid⟩
  rw [mv.refund, hr]
  exact Int.zero_add _

/-- **The message under the moment's facts.** -/
theorem swap_core {msg : Msg} {w : Jaune.State} {E : Adr} {i j : Fin 3} {dx dy minDy amp DD : Nat}
    (mf : MomentFacts w) (mk : ExitMarked w) (e : Asked msg w E (swapCalldata i j dx minDy)) (req : SwapRequest w E i j dx dy minDy)
    (hfee : word w pool feeSlot ≤ feeDen) (haf : word w pool adminFeeSlot ≤ feeDen)
    (hdyq : dy = quote w msg.benv.stat.time.toNat i j dx) (hA : ampAt w msg.benv.stat.time.toNat = some amp) (hinv : invariant w amp = some DD) :
    ∃ admin, swapAdmin w msg.benv.stat.time.toNat i j dx = some admin ∧ ∀ R, callRoom ≤ R →
      R + swapFrameGas w E msg.benv.stat.time.toNat amp i j dx dy (scaled w i + netOf w i dx * rates.get i / precision) DD (decide (allowanceOf w E i = 2 ^ 256 - 1)) < 2 ^ 256 →
      ∃ post, exec (initEvm (msg.withGas (R + swapFrameGas w E msg.benv.stat.time.toNat amp i j dx dy (scaled w i + netOf w i dx * rates.get i / precision) DD
          (decide (allowanceOf w E i = 2 ^ 256 - 1))))) = .ok post ∧ post.error = none ∧ post.gasLeft = R ∧
        post.refundCounter = ((swapRefund w E i j dx dy (allowanceOf w E i) : Nat) : Int) ∧ post.accountsToDelete.toList = [] ∧
        SwapPaid w post.state E i j dx dy admin := by
  obtain ⟨s, hck0, hck, hco, hto, hC, hcode, hid⟩ := asked_facts mf mk e
  have ht : msg.currentTarget = pool := e.entry.named.1
  have hcaller : msg.caller = E := e.entry.named.2.1
  have hopen := e.coinsOpen
  have hfork : CoveredFork (initSevm msg).benvStat.fork := e.entry.plain.2.2.2
  have hdata : (initSevm msg).data = swapCalldata i j dx minDy := e.data
  have hstor : ∀ x ∈ parties w, (initDevm msg).getStor x = w.getStor x := fun x hx => congrArg Acct.stor (e.entry.world x hx).1
  have hσ : (initDevm msg).getStor (initSevm msg).currentTarget = w.getStor pool := by
    show (initDevm msg).getStor msg.currentTarget = _
    rw [ht]
    exact hstor pool List.mem_cons_self
  have hcoinS : ∀ k : Fin 3, (initDevm msg).getStor (coinAt k) = w.getStor (coinAt k) := fun k => hstor _ (by
    match k with
    | 0 => simp only [coinAt, parties, List.mem_cons, true_or, or_true]
    | 1 => simp only [coinAt, parties, List.mem_cons, true_or, or_true]
    | 2 => simp only [coinAt, parties, List.mem_cons, true_or, or_true])
  obtain ⟨w4, w36, w68, w100⟩ := swap_words hdata
  have hiw : exI (initSevm msg) = Nat.toB256 i.val := w4
  have hjw : exJ (initSevm msg) = Nat.toB256 j.val := w36
  have hdxw : exDx (initSevm msg) = Nat.toB256 dx := w68
  have hmdw : exMinDy (initSevm msg) = Nat.toB256 minDy := w100
  obtain ⟨hLive, hij, ⟨hdx0, hmin, hdy0⟩, ⟨hle, hal⟩, hPF, ⟨⟨hcrP, hcrE⟩, ⟨hfeeI, hfeeJ⟩, hfit⟩, hap⟩ := req
  have hdxN : dx < 2 ^ 256 := Nat.lt_of_le_of_lt hle coinHeld_lt
  have hq : swapOut w msg.benv.stat.time.toNat i j dx = some dy := by
    unfold quote at hdyq
    cases h : swapOut w msg.benv.stat.time.toNat i j dx with
    | none => rw [h] at hdyq; simp only [Option.getD_none] at hdyq; omega
    | some q => rw [h] at hdyq; simp only [Option.getD_some] at hdyq; rw [hdyq]
  have hkill : s.isKilled = false := by
    have h0 : (w.getStor pool).get isKilledSlot = 0 := B256.toNat_inj _ _ hLive
    have h1 := hck0.abs.isKilled
    rw [h0] at h1
    cases hs : s.isKilled with
    | false => rfl
    | true => rw [hs] at h1; exact absurd h1 (by decide)
  have hbi : recorded w i + netOf w i dx < 2 ^ 256 := books_credit_lt (mk.covered i) hcrP
  have hdy190 := swapOut_lt hq hfit
  have hmdN : minDy < 2 ^ 256 := Nat.lt_of_le_of_lt hmin (Nat.lt_trans hdy190 (by decide))
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = swapB1 (initSevm msg) (initDevm msg) i := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = swapB2 (initSevm msg) (initDevm msg) i := ⟨_, rfl⟩
  have hTt : (initSevm msg).currentTarget = pool := ht
  have hTc : (initSevm msg).caller = E := hcaller
  have hcoi := hco i
  obtain ⟨hBw, hnet⟩ := swap_B hB1 hB2 hcoi (hcoinS i) hTt hTc hdxw mk hap hdxN hfeeI hcrP
  have hE0 : E ≠ 0 := e.nonzero
  obtain ⟨x0, x1, x2, v, admin, hi3, hj3, hadm, M⟩ := swap_model (e0 := initSevm msg) (σ := (initDevm msg).getStor (initSevm msg).currentTarget) (s0 := s) (B1 := B1) (B2 := B2)
    hσ hck.abs hkill hij hiw hjw hdxw hmdw hdxN hmdN hnet hinv hA hfee haf hq hmin hfit hbi
  have hiN : i.val = (exI (initSevm msg)).toNat := by rw [hiw, B256.toNat_toB256_of_lt (by have := i.isLt; omega)]
  have hjN : j.val = (exJ (initSevm msg)).toNat := by rw [hjw, B256.toNat_toB256_of_lt (by have := j.isLt; omega)]
  have hdyN : dy < 2 ^ 256 := Nat.lt_trans hdy190 (by decide)
  obtain ⟨O, hO⟩ : ∃ O, O = exDyOut (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) ((w.getStor pool).get feeSlot) (exRate (exJ (initSevm msg)).toNat) := ⟨_, rfl⟩
  obtain ⟨F0, hF0⟩ : ∃ F0, F0 = exDyFee (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) ((w.getStor pool).get feeSlot) := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = exAdm F0 ((w.getStor pool).get adminFeeSlot) (exRate (exJ (initSevm msg)).toNat) := ⟨_, rfl⟩
  have hOn : O.toNat = dy := by have := M.On; rw [hσ] at this; rw [hO]; exact this
  have hAn : A0.toNat = admin := by have := M.An; rw [hσ, ← hF0] at this; rw [hA0]; exact this
  have hOw : O = Nat.toB256 dy := by rw [← hOn, toB256_toNat]
  have hChain := swap_chain_of (B1 := B1) (B2 := B2) e hck0 hco hap hij hiw hjw hdxw hE0 hinv M hσ hO hF0 hA0 hOn hAn hle hal hcrP hcrE hfeeI hfeeJ hdx0 hdy0 hbi (mk.covered j)
  have hbounds := swap_debit_bounds (initSevm msg) (initDevm msg) i j
  have hlt : exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 amp v < 2 ^ 200 :=
    ex_cost_lt (K := 200000) (by decide) hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
  have hlen : (initSevm msg).data.length = 132 := by rw [hdata]; exact swapCalldata_length
  have hsel := swap_selector hdata
  have hdep : 2 ≤ (initSevm msg).depth := e.entry.plain.2.2.1
  have hstatic : (initSevm msg).isStatic = false := e.entry.plain.2.1
  have hval : (initSevm msg).value = 0 := e.entry.plain.1
  have hkillW : ((initDevm msg).getStor (initSevm msg).currentTarget).get isKilledSlot = 0 := by
    rw [hσ]; exact B256.toNat_inj _ _ hLive
  have hpf : PullFitsK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).caller (initSevm msg).currentTarget (exDx (initSevm msg)) := by
    rw [hcoi, hcoinS, hTt, hTc, hdxw]
    exact pull_fits hopen hE0 hap hPF i hdxN hle hal hcrP (fun _ => hfeeI)
  have hqf : PushFitsK j ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) j)) (initSevm msg).currentTarget (initSevm msg).caller
      (exDyOut (exW3 x0 x1 x2 (exJ (initSevm msg)).toNat) (Nat.toB256 v) (((initDevm msg).getStor (initSevm msg).currentTarget).get feeSlot) (exRate (exJ (initSevm msg)).toNat)) := by
    rw [hco j, hcoinS, hσ, ← hO, hOw, hTt, hTc]
    exact push_fits hopen hE0 hap.toCoinsApart j hdyN (dy_le_held M.room (mk.covered j)) hcrE (fun _ => hfeeJ)
  have hrun : ∀ {R : Nat}, 2201 ≤ R → R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 B1 B2 amp v < 2 ^ 256 → _ :=
    fun {R} hR hG => swap_floor_run (msg := msg) (s0 := s) (i := i) (j := j) (amp := amp) (v := v) (x0 := x0) (x1 := x1) (x2 := x2) (R := R) hcode hfork hstatic hdep (by rw [hlen]; decide) (by rw [hlen]; decide) hsel hid hC hij hiN hjN hck.abs hck.unlocked hval hkillW hi3 hj3 M.hX
      (by rw [← hB1, ← hB2]; exact M.sub) hpf hqf (fun h => (hBw h).2.2)
      (by rw [← hB1, ← hB2]; exact M.hmx) (by rw [← hB1, ← hB2]; exact M.hax) M.hA (by rw [← hB1, ← hB2]; exact M.hres) M.hy1 M.hy2 M.hmf M.hsf M.hmo M.hmin M.hma M.hmap
      (by rw [← hB1, ← hB2]; exact M.hbi) M.hbj1 M.hbj2 hR (by rw [← hB1, ← hB2]; exact hG)
  subst hB1 hB2
  exact ⟨admin, hadm, swap_finish e hChain hrun hlt⟩

/-- **`swap_message`.** -/
theorem swap_message_holds : swap_message := by
  intro d m A msg E i j dx minDy admin amp D x t ask ht req hin hadm R hR hG
  subst ht
  obtain ⟨hA, hD, rfl⟩ := hin
  have fees := m.feesWithin A
  obtain ⟨admin', h1, h2⟩ := swap_core (m.facts A) (m.marked A ask.coinsOpen.usdcParties.1) ask req fees.1 fees.2 rfl hA hD
  obtain rfl : admin' = admin := Option.some.inj (h1.symm.trans hadm)
  obtain ⟨post, hx, herr, hg, hrf, -, hpaid⟩ := h2 R hR hG
  exact ⟨post, hx, herr, hg, by rw [hrf, Int.toNat_natCast], hpaid⟩

/-! ## The transaction -/

/-- The observers read only the four contracts. -/
theorem SwapPaid.congr {w w₁ w₂ : Jaune.State} {E : Adr} {i j : Fin 3} {dx dy admin : Nat} (h : SwapPaid w w₁ E i j dx dy admin)
    (hs : ∀ x, x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt → w₂.getStor x = w₁.getStor x) :
    SwapPaid w w₂ E i j dx dy admin := by
  have hp := hs pool (by simp only [true_or])
  have hd := hs dai (by simp only [true_or, or_true])
  have hu := hs usdc (by simp only [true_or, or_true])
  have ht := hs usdt (by simp only [or_true])
  have hcoin : ∀ x k, coinHeld w₂ x k = coinHeld w₁ x k := by
    intro x k
    unfold coinHeld UsdcPacked word
    rw [hu]
    match k with
    | 0 => simp only [coinAt, hd]
    | 1 => simp only [coinAt, hu]
    | 2 => simp only [coinAt, ht]
  have hrec : ∀ k, recorded w₂ k = recorded w₁ k := fun k => by
    unfold recorded word
    rw [hp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrec]; exact h.booksIn
  · rw [hrec]; exact h.booksOut
  · rw [hcoin, hcoin]; exact h.coinsIn
  · rw [hcoin, hcoin]; exact h.coinsOut

theorem swapFrameGas_ge (w : Jaune.State) (E : Adr) (t amp : Nat) (i j : Fin 3) (dx dy x D : Nat) (u : Bool) : 50000 ≤ swapFrameGas w E t amp i j dx dy x D u := by
  have hb : 50000 ≤ pullBase i := by
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
  unfold swapFrameGas pullGas
  omega

/-- What an admissible `exchange`'s spend comes to. -/
theorem swapSpent_parts {w : Jaune.State} {data : Bytes} {E : Adr} {t : Nat} {i j : Fin 3} {dx spent : Nat}
    (h : swapSpent w data E t i j dx = some spent) :
    ∃ amp D, ampAt w t = some amp ∧ invariant w amp = some D ∧ ∃ dy, swapOut w t i j dx = some dy ∧
      spent = callIntrinsic data + swapFrameGas w E t amp i j dx dy (scaled w i + netOf w i dx * rates.get i / precision) D (decide (allowanceOf w E i = 2 ^ 256 - 1)) := by
  unfold swapSpent at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨amp, hamp, D, hD, a, ha, b, hb, x, hx, dy, hdy, rfl⟩ := h
  refine ⟨amp, D, hamp, hD, dy, hdy, ?_⟩
  have e1 := Blanc.StableSwapNewton.chkMul_some ha
  have e2 := (Blanc.StableSwapNewton.chkDiv_some hb).1
  have e3 := Blanc.StableSwapNewton.chkAdd_some hx
  rw [e3, e2, e1]

/-- **`swap`.** -/
theorem swap_holds : swap := by
  intro d m A tx E i j dx minDy spent hdata hspent adm hopen req
  obtain ⟨prio, maxFee, form, ready⟩ := adm.form
  have mf := m.facts A
  have mk := m.marked A hopen.usdcParties.1
  have fees := m.feesWithin A
  have hw : m.benv.state = m.world := rfl
  have hstatFork := adm.fork
  obtain ⟨amp, D, hA, hD, dy, hq, hsp⟩ := swapSpent_parts hspent
  have hdyq : quote m.world m.benv.stat.time.toNat i j dx = dy := by
    unfold quote
    rw [hq]
    rfl
  rw [hdyq] at req ⊢
  obtain ⟨-, -, -, -, -, -, f, -, -, -, -, -, -, d2, p2, -, -, -, -, hadm⟩ := swapOut_parts hq
  obtain ⟨F, hF⟩ : ∃ F, F = swapFrameGas m.world E m.benv.stat.time.toNat amp i j dx dy (scaled m.world i + netOf m.world i dx * rates.get i / precision) D (decide (allowanceOf m.world E i = 2 ^ 256 - 1)) := ⟨_, rfl⟩
  rw [← hF] at hsp
  obtain ⟨admin, hadmE⟩ : ∃ admin, admin = f * word m.world pool adminFeeSlot / feeDen * precision / rates.get j := ⟨_, rfl⟩
  rw [← hadmE] at hadm
  have hroom : GasRoom m.benv m.bout tx (callIntrinsic tx.data + F + callRoom) := by
    have := adm.room
    rw [hsp] at this
    exact this
  obtain ⟨debit, post, bout', hqq, process, cum⟩ := tx_of_frame (r := swapRefund m.world E i j dx dy (allowanceOf m.world E i)) (F := F) (index := m.nextIndex)
    (Q := fun _ p => p.accountsToDelete.toList = [] ∧ SwapPaid m.world p.state E i j dx dy admin)
    adm.fork form ready hroom
    (by rw [hdata]; exact swapCalldata_length)
    (by rw [hF]; exact swapFrameGas_ge ..)
    (by rw [hw, mf.poolCode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel))
    (by
      have h := (parties_not_precomp hstatFork.histFork).1
      show (Fork.ruleSet m.benv.stat.fork).isPrecomp pool = false
      exact Blanc.Composition.Curve3Pool3CrvHeadlines.precomp_false h)
    (by
      intro debit msg after hd hp he
      obtain ⟨M, hmM, haM, ce0, hFd, htime⟩ := tx_asked mf mk form ready adm hopen hd hp he
      subst hmM
      subst haM
      have ce : Asked msg m.world E (swapCalldata i j dx minDy) := by rw [← hdata]; exact ce0
      obtain ⟨admin', h1, h2⟩ := swap_core mf mk ce req fees.1 fees.2 (by rw [htime]; exact hdyq.symm) (by rw [htime]; exact hA) hD
      rw [htime] at h1 h2
      obtain rfl : admin' = admin := Option.some.inj (h1.symm.trans hadm)
      have hneed := hroom.enough
      have hcap := hroom.cap
      have hR : callRoom = 2201 := rfl
      have hsum : tx.gas - (callIntrinsic tx.data + F) + F = msg.gas := by
        rw [hFd]; omega
      rw [← hF] at h2
      obtain ⟨post, hx, herr, hg, hrf, hdel, hpaid⟩ := h2 (tx.gas - (callIntrinsic tx.data + F)) (by omega) (by rw [hsum, hFd]; omega)
      rw [hsum] at hx
      exact ⟨post, hx, herr, hg, hrf, hdel, hpaid⟩)
  obtain ⟨hdel, hpaid⟩ := hqq
  refine ⟨_, bout', afterRefund (callIntrinsic tx.data + F) (swapRefund m.world E i j dx dy (allowanceOf m.world E i)), admin, process, ?_, cum, hadm, ?_⟩
  · show swapGasUsed m.world tx.data E m.benv.stat.time.toNat i j dx = _
    unfold swapGasUsed
    rw [hspent, hq, hsp]
    rfl
  · rw [hdel]
    exact hpaid.congr (tx_end_stor mf mk form ready adm post)

end Blanc.Composition.Curve3PoolPublic
