import Blanc.Composition.Curve3PoolExitMain
import Blanc.Composition.Curve3PoolSwapBound
import Blanc.Composition.Curve3PoolSwapRequest

/-!
# `swap`: the run, the message and the transaction

`swap_floor_run`: the frame's run at any residual `R ≥ 2201`, from the model's words and the coins' fits, ending as
`ExFrameEnd` says.
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
      hbi := hbi', hbj1 := hbj1, hbj2 := hbj2, xN := xN, Dn := Dn, xvN := xvN, On := r2, An := r3, room := g.room }⟩

/-! ## The debits -/

theorem swap_debit_bounds (e d : _) (i j : Fin 3) (hx : True) :
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

end Blanc.Composition.Curve3PoolPublic
