import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactBack
import Blanc.Lift.Curve3Pool.Walk.AlLiveFrame

/-!
# `add_liquidity`, exact: the byte-level walk

`rx_al_frame1_exact` (positive supply) and `rx_al_frame0_exact` (first deposit): with the calls'
data `P` and its exact premises fixed first, every residual gas `R` above the headroom threshold
runs the certificate's entry tree from `R + alExactCost1` (resp. `alExactCost0`) to `STOP` with
exactly `R` left, at the bounded walk's end (`AlEnd`). The walk is the existing one: the
dispatcher, the prologue core `rx_al_preE`, `D0` (`rx_al_d0E`, positive supply), the pull loop
(`rx_al_loopX`), and the back half (`rx_al_back1X` / `rx_al_back0X`), each call answered by its
exact profile (`ExactE`).

The cost is closed: a function of the entry (`pre`, `sevm`), the supply `T`, the fee coin's
balances `B1`, `B2`, the calls' data `P`, `amp`, and the model's intermediate words (`get_D_mem`
inputs and results, the fee iterations' words). The memory is the canonical one: `vyMem` of the
empty memory at the dispatcher, then each stage's literal successor; the bases are the canonical
successors from `pre`. The threshold `100000 + 5 U` is headroom, separate from the cost.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section Front

variable (sevm : Sevm) (pre : Devm) (P : ALExactCalls) (amp : Nat)

/-- The memory the dispatcher leaves. -/
abbrev alMv : Mem := vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- The `totalSupply()` call's canonical successor. -/
def alSupNext : Devm :=
  P.supplyNext (alSupBase sevm pre) [] (alSupMem sevm pre (alMv sevm)
    (pre.getStor sevm.currentTarget) amp)

/-- The canonical base at the supply test. -/
def alFN1 : Devm := alPreBase2 sevm (alSupNext sevm pre P amp)

/-- The canonical memory at the supply test. -/
def alFM1 (T : B256) : Mem :=
  alPreMem2 (alSupMem sevm pre (alMv sevm) (pre.getStor sevm.currentTarget) amp)
    (alSupNext sevm pre P amp).returnData T (pre.getStor sevm.currentTarget)

/-- **The front's exact charge**: the dispatcher (`315`), the prologue before the call, the
`totalSupply()` debit and the prologue after it. -/
def alFrontCost : Nat :=
  315 + alPreCost1 sevm pre +
    P.supplyDebit (alSupBase sevm pre) [] (alSupMem sevm pre (alMv sevm)
      (pre.getStor sevm.currentTarget) amp) +
    alPreCost2 sevm (alSupNext sevm pre P amp)

/-- The canonical memory after `D0`. -/
def alFM0 (T : B256) (xa : V3) (v0 : Nat) : Mem :=
  alD0Mem (alFM1 sevm pre P amp T) (balAt (pre.getStor sevm.currentTarget) 0)
    (balAt (pre.getStor sevm.currentTarget) 1) (balAt (pre.getStor sevm.currentTarget) 2)
    (Nat.toB256 amp) xa v0

/-- `D1`'s context charge: `29` from `0x840` (last amount zero), `9` from `0x900`. -/
def alD1c0 : Nat := if alAmt sevm 2 = 0 then 29 else 9

/-- **`add_liquidity`'s exact charge on a positive supply.** -/
def alExactCost1 (T B1 B2 : B256) (xa xb xc : V3) (v0 v1 v2 : Nat)
    (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256) : Nat :=
  alFrontCost sevm pre P amp + (2515 + costGetDMem xa amp) +
    alLoopCost sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
      (alFM0 sevm pre P amp T xa v0) B1 B2 T (alOld (pre.getStor sevm.currentTarget)) +
    alBack1Cost sevm P
      (alLN3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alLM3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alD1c0 sevm) (Nat.toB256 amp) (Nat.toB256 v0) T (alOld (pre.getStor sevm.currentTarget))
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) xb xc v1 v2
      f0 f1 f2 s0 s1 s2 x0 x1 x2

/-- **`add_liquidity`'s exact charge on a first deposit.** -/
def alExactCost0 (B1 B2 : B256) (xb : V3) (v1 : Nat) : Nat :=
  alFrontCost sevm pre P amp +
    alLoopCost sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
      (alFM1 sevm pre P amp 0) B1 B2 0 (alOld (pre.getStor sevm.currentTarget)) +
    alBack0Cost sevm P
      (alLN3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM1 sevm pre P amp 0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alLM3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM1 sevm pre P amp 0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alD1c0 sevm) (Nat.toB256 amp)
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) xb v1

end Front

theorem alPreBase2_congr {sevm : Sevm} {d e : Devm} (h : Devm.EqModGas d e) :
    Devm.EqModGas (alPreBase2 sevm d) (alPreBase2 sevm e) :=
  ((h.afterSload sevm _).afterSload sevm _).afterSload sevm _

theorem alPreCost2_congr {sevm : Sevm} {d e : Devm} (h : Devm.EqModGas d e) :
    alPreCost2 sevm d = alPreCost2 sevm e := by
  unfold alPreCost2
  rw [h.sloadCost_congr, (h.afterSload sevm _).sloadCost_congr,
    ((h.afterSload sevm _).afterSload sevm _).sloadCost_congr]

/-- The coins as the locked storage reads them. -/
theorem coinAt_locked (σ : Stor) {k : Nat} (hk : k < 3) : coinAt (alLocked1 σ) k = coinAt σ k :=
  Stor.get_set_ne _ (coin_ne_lock hk) _

section Frame

variable {sevm : Sevm} {pre : Devm} {s : State} {U amp : Nat} {T B1 B2 : B256}
  {W : Nat → Devm → Prop}

/-- **`add_liquidity` on a positive supply, the whole frame forward, exact.** -/
theorem rx_al_frame1_exact {xa xb xc : V3} {v0 v1 v2 : Nat} {f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    (P : ALExactCalls)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity) (hid : IdReady sevm pre)
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hP : ALExactPremises sevm (pre.getStor sevm.currentTarget) T B1 B2
      (alMintW T (Nat.toB256 v0) (Nat.toB256 v2)) W U P)
    (hskip : ∀ k, k < 3 → alAmt sevm k = 0 → ∀ b, W k b → W (k + 1) b)
    (hT : T ≠ 0) (hnz : ¬ (alAmt sevm 0 = 0 ∧ alAmt sevm 1 = 0 ∧ alAmt sevm 2 = 0))
    (hsub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1)
    (a0 : ¬ balAt (pre.getStor sevm.currentTarget) 0 + alAmt sevm 0 <
      balAt (pre.getStor sevm.currentTarget) 0)
    (a1 : ¬ balAt (pre.getStor sevm.currentTarget) 1 + alAmt sevm 1 <
      balAt (pre.getStor sevm.currentTarget) 1)
    (a2 : ¬ balAt (pre.getStor sevm.currentTarget) 2 + alCr2 sevm B1 B2 <
      balAt (pre.getStor sevm.currentTarget) 2)
    (hX0 : xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some xa)
    (hD0 : getDChk xa.get amp 1 = some v0)
    (hXb : xpChk ⟨(alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0).toNat,
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1).toNat,
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get amp 1 = some v1) (hlt : Nat.toB256 v0 < Nat.toB256 v1)
    (h0 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 0)
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0) f0 s0 x0)
    (h1 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 1)
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1) f1 s1 x1)
    (h2 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 2)
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2) f2 s2 x2)
    (hXc : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc)
    (hD2 : getDChk xc.get amp 1 = some v2)
    (hge : ¬ Nat.toB256 v2 < Nat.toB256 v0) (hmul : B256.Nofm T (Nat.toB256 v2 - Nat.toB256 v0))
    (hD00 : Nat.toB256 v0 ≠ 0)
    (hslip : ¬ alMintW T (Nat.toB256 v0) (Nat.toB256 v2) <
      Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ T + alMintW T (Nat.toB256 v0) (Nat.toB256 v2) < T)
    {R : Nat} (hR : 100000 + 5 * U ≤ R)
    (hGb : R + alExactCost1 sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 +
      6000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty
        (R + alExactCost1 sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))
      t_0000_c0
      (AlEndX sevm (alUnlock (alStor3 (alLocked1 (pre.getStor sevm.currentTarget)) s0 s1 s2))
        f0 f1 f2 R) := by
  obtain ⟨hsup, hpull, hbalB, hbalA, hmint⟩ := hP
  unfold alExactCost1 alFrontCost at hGb ⊢
  rw [show ∀ a b c d e f, R + (315 + a + b + c + d + e + f) =
      (R + f + e + d + c + b + a) + 315 by intros; omega]
  refine rx_dispatch_al hlen hcd hsel ?_
  refine rx_al_preE (R := 0) (E := ExactE P.supplyDebit P.supplyNext) hfork hstatic hcd
    ⟨fun _ => rfl, hid, hWc 0 (by decide), hWb⟩ ha hlock hval hkill hA
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _) (vyMem_empty_size _)
    (StaticWordCallProfile.okE hsup) hmf (by omega) (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wf0 wf1 wf2 wF wAF wAw wT wD0 wb0 wb1 wb2 _ _ Gs d
    hE hG1 hd hb1 hM1
  obtain ⟨hEg, hEn⟩ := hE
  have hAw' : Aw = Nat.toB256 amp := by rw [← hAw, toB256_toNat]
  subst hAw'
  have hc2 : alPreCost2 sevm d = alPreCost2 sevm (alSupNext sevm pre P amp) := alPreCost2_congr hEn
  refine ⟨fun h => absurd h hT, fun _ => ?_⟩
  have hg1 : g1 = (R + alBack1Cost sevm P (alLN3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alLM3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alD1c0 sevm) (Nat.toB256 amp) (Nat.toB256 v0) T (alOld (pre.getStor sevm.currentTarget))
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) xb xc v1 v2
      f0 f1 f2 s0 s1 s2 x0 x1 x2 +
      alLoopCost sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
      (alFM0 sevm pre P amp T xa v0) B1 B2 T (alOld (pre.getStor sevm.currentTarget))) + (2515 + costGetDMem xa (Nat.toB256 amp).toNat) := by
    have hdeb : P.supplyDebit (alSupBase sevm pre) []
        (alSupMem sevm pre (vyMem Mem.empty (Sevm.dataWord sevm 0)) (pre.getStor sevm.currentTarget) amp) =
        P.supplyDebit (alSupBase sevm pre) []
        (alSupMem sevm pre (alMv sevm) (pre.getStor sevm.currentTarget) amp) := rfl
    rw [hAw]; omega
  rw [hg1]
  have hn1 : Devm.EqModGas b1 (alFN1 sevm pre P amp) := by rw [hb1]; exact alPreBase2_congr hEn
  have hM1' : M1 = alFM1 sevm pre P amp T := by rw [hM1, hEn.returnData]; rfl
  refine rx_al_d0E (R := 0) (S := []) hX0 (by rw [hAw]; exact hD0) hR1 hW1 hsz1 wf0 wf1 wf2 wF wAF
    wAw wT wb0 wb1 wb2 (by omega) (by simp only [List.length_nil]; omega) ?_
  intro M2 img2 g2 hR2 hW2 hsz2 vf0 vf1 vf2 vF vAF vAw vT vD0 vb0 vb1 vb2 _ _ hG2 hM2
  obtain rfl : g2 = R + alBack1Cost sevm P (alLN3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alLM3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
      (alD1c0 sevm) (Nat.toB256 amp) (Nat.toB256 v0) T (alOld (pre.getStor sevm.currentTarget))
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) xb xc v1 v2
      f0 f1 f2 s0 s1 s2 x0 x1 x2 +
      alLoopCost sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
      (alFM0 sevm pre P amp T xa v0) B1 B2 T (alOld (pre.getStor sevm.currentTarget)) := by omega
  rw [hM1'] at hM2
  have hback : ∀ (s' c0 : Nat) (X : SFunc), ((s' = 0x840 ∧ c0 = 29 ∧ X = t_1333_c41) ∨
      (s' = 0x900 ∧ c0 = 9 ∧ X = t_1333_c6)) → alD1c0 sevm = c0 → ∀ (b' : Devm) (M' : Mem)
      (img' : Bytes), ExLive sevm (W 3) b' (alLocked1 (pre.getStor sevm.currentTarget)) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = s' →
      AlPullImg img' 3 (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
        ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 amp) T (Nat.toB256 v0)
        (alOld (pre.getStor sevm.currentTarget))
        (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) →
      Devm.EqModGas b' (alLN3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P
        (alFN1 sevm pre P amp) (alFM0 sevm pre P amp T xa v0) B1 B2
        (alOld (pre.getStor sevm.currentTarget))) →
      M' = alLM3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)) →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: []) M'
        (R + alBack1Cost sevm P (alLN3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P
          (alFN1 sevm pre P amp) (alFM0 sevm pre P amp T xa v0) B1 B2
          (alOld (pre.getStor sevm.currentTarget)))
        (alLM3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
          (alFM0 sevm pre P amp T xa v0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
        (alD1c0 sevm) (Nat.toB256 amp) (Nat.toB256 v0) T (alOld (pre.getStor sevm.currentTarget))
        (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) xb xc v1 v2
        f0 f1 f2 s0 s1 s2 x0 x1 x2)) X
      (AlEndX sevm (alUnlock (alStor3 (alLocked1 (pre.getStor sevm.currentTarget)) s0 s1 s2))
        f0 f1 f2 R) := by
    intro s' c0 X hctx hc0 b' M' img' hL' hR' hW' hsz' hm' hn' hM'
    rw [hc0]
    rw [hc0] at hGb
    exact rx_al_back1X (P := P) hfork hstatic hctx hL' (hWc 4 (by decide)) hR' hW' hsz' hm' hXb
      (by rw [hAw]; exact hD1) hlt hT h0 h1 h2 hXc (by rw [hAw]; exact hD2) hge hmul hD00 hslip hadd
      (by rw [al_stor3_tok, Stor.get_set_ne _ (by decide)]; exact hmint) hn' hM' (by omega)
      (by omega)
  refine rx_al_loopX (n := alFN1 sevm pre P amp) (m := alFM0 sevm pre P amp T xa v0) (P := P)
    (B1 := B1) (B2 := B2) (W := W) (old := alOld (pre.getStor sevm.currentTarget))
    (F := cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
    (AF := (pre.getStor sevm.currentTarget).get adminFeeSlot) (A := Nat.toB256 amp) (T := T)
    (D0 := Nat.toB256 v0) hfork hdepth hL1 hR2 hW2 (by rw [ite_eq_right hT]; exact hsz2)
    ⟨vf0, vf1, vf2, vF, vAF, vAw, vT, vD0, vb0, vb1, vb2⟩ hn1 hM2 (fun h => absurd h hT) hnz
    (fun j hj => hWc j (by omega)) (hskip 0 (by decide)) (hskip 1 (by decide))
    (hskip 2 (by decide))
    (fun k hk ha => by rw [coinAt_locked _ hk]; exact hpull k hk ha)
    (fun h => by rw [coinAt_locked _ (by decide)]; exact hbalB h)
    (fun h => by rw [coinAt_locked _ (by decide)]; exact hbalA h) hsub a0 a1 a2 (by omega)
    (by omega) ?_ ?_
  · intro ha2 b' M' img' hL' hR' hW' hsz' hm' hn' hM'
    exact hback 0x840 29 t_1333_c41 (.inl ⟨rfl, rfl, rfl⟩)
      (by unfold alD1c0; rw [ite_eq_left ha2]) b' M' img' hL' hR' hW' hsz' hm' hn' hM'
  · intro ha2 b' M' img' hL' hR' hW' hsz' hm' hn' hM'
    exact hback 0x900 9 t_1333_c6 (.inr ⟨rfl, rfl, rfl⟩)
      (by unfold alD1c0; rw [ite_eq_right ha2]) b' M' img' hL' hR' hW' hsz' hm' hn' hM'

/-- **`add_liquidity` on a first deposit, the whole frame forward, exact.** -/
theorem rx_al_frame0_exact {xb : V3} {v1 : Nat} (P : ALExactCalls)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity) (hid : IdReady sevm pre)
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hP : ALExactPremises sevm (pre.getStor sevm.currentTarget) 0 B1 B2 (Nat.toB256 v1) W U P)
    (hskip : ∀ k, k < 3 → alAmt sevm k = 0 → ∀ b, W k b → W (k + 1) b)
    (ht0 : alAmt sevm 0 ≠ 0 ∧ alAmt sevm 1 ≠ 0 ∧ alAmt sevm 2 ≠ 0)
    (hsub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1)
    (a0 : ¬ balAt (pre.getStor sevm.currentTarget) 0 + alAmt sevm 0 <
      balAt (pre.getStor sevm.currentTarget) 0)
    (a1 : ¬ balAt (pre.getStor sevm.currentTarget) 1 + alAmt sevm 1 <
      balAt (pre.getStor sevm.currentTarget) 1)
    (a2 : ¬ balAt (pre.getStor sevm.currentTarget) 2 + alCr2 sevm B1 B2 <
      balAt (pre.getStor sevm.currentTarget) 2)
    (hXb : xpChk ⟨((alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) 0).toNat,
      ((alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) 1).toNat,
      ((alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get amp 1 = some v1) (hlt : 0 < Nat.toB256 v1)
    (hslip : ¬ Nat.toB256 v1 < Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ 0 + Nat.toB256 v1 < 0)
    {R : Nat} (hR : 100000 + 5 * U ≤ R)
    (hGb : R + alExactCost0 sevm pre P amp B1 B2 xb v1 + 6000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + alExactCost0 sevm pre P amp B1 B2 xb v1))
      t_0000_c0
      (AlEndX sevm (alUnlock (alStor3 (alLocked1 (pre.getStor sevm.currentTarget))
        ((alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) 0) ((alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) 1) ((alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) 2))) 0 0 0 R) := by
  obtain ⟨hsup, hpull, hbalB, hbalA, hmint⟩ := hP
  unfold alExactCost0 alFrontCost at hGb ⊢
  rw [show ∀ a b c d e, R + (315 + a + b + c + d + e) = (R + e + d + c + b + a) + 315
    by intros; omega]
  refine rx_dispatch_al hlen hcd hsel ?_
  refine rx_al_preE (R := 0) (E := ExactE P.supplyDebit P.supplyNext) hfork hstatic hcd
    ⟨fun _ => rfl, hid, hWc 0 (by decide), hWb⟩ ha hlock hval hkill hA
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _) (vyMem_empty_size _)
    (StaticWordCallProfile.okE hsup) hmf (by omega) (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wf0 wf1 wf2 wF wAF wAw wT wD0 wb0 wb1 wb2 _ _ Gs d
    hE hG1 hd hb1 hM1
  obtain ⟨hEg, hEn⟩ := hE
  have hAw' : Aw = Nat.toB256 amp := by rw [← hAw, toB256_toNat]
  subst hAw'
  have hc2 : alPreCost2 sevm d = alPreCost2 sevm (alSupNext sevm pre P amp) := alPreCost2_congr hEn
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  have hg1 : g1 = R + alBack0Cost sevm P (alLN3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
          (alFM1 sevm pre P amp 0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
        (alLM3 sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
          (alFM1 sevm pre P amp 0) B1 B2 (alOld (pre.getStor sevm.currentTarget)))
        (alD1c0 sevm) (Nat.toB256 amp) (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2) xb v1 +
      alLoopCost sevm (alLocked1 (pre.getStor sevm.currentTarget)) P (alFN1 sevm pre P amp)
        (alFM1 sevm pre P amp 0) B1 B2 0 (alOld (pre.getStor sevm.currentTarget)) := by
    have hdeb : P.supplyDebit (alSupBase sevm pre) []
        (alSupMem sevm pre (vyMem Mem.empty (Sevm.dataWord sevm 0)) (pre.getStor sevm.currentTarget) amp) =
        P.supplyDebit (alSupBase sevm pre) []
        (alSupMem sevm pre (alMv sevm) (pre.getStor sevm.currentTarget) amp) := rfl
    omega
  rw [hg1]
  have hn1 : Devm.EqModGas b1 (alFN1 sevm pre P amp) := by rw [hb1]; exact alPreBase2_congr hEn
  have hM1' : M1 = alFM1 sevm pre P amp 0 := by rw [hM1, hEn.returnData]; rfl
  have hmm : Mem.EqExcept M1 (alFM1 sevm pre P amp 0) fun _ => False := by
    rw [← hM1']; exact Mem.EqExcept.refl hW1 _
  refine rx_al_loopX (n := alFN1 sevm pre P amp) (m := alFM1 sevm pre P amp 0) (P := P)
    (B1 := B1) (B2 := B2) (W := W) (old := alOld (pre.getStor sevm.currentTarget))
    (F := cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
    (AF := (pre.getStor sevm.currentTarget).get adminFeeSlot) (A := Nat.toB256 amp) (T := 0)
    (D0 := 0) hfork hdepth hL1 hR1 hW1 (by rw [ite_eq_left rfl]; exact hsz1)
    ⟨wf0, wf1, wf2, wF, wAF, wAw, wT, wD0, wb0, wb1, wb2⟩ hn1 hmm (fun _ => ht0)
    (fun h => ht0.1 h.1) (fun j hj => hWc j (by omega)) (hskip 0 (by decide))
    (hskip 1 (by decide)) (hskip 2 (by decide))
    (fun k hk ha => by rw [coinAt_locked _ hk]; exact hpull k hk ha)
    (fun h => by rw [coinAt_locked _ (by decide)]; exact hbalB h)
    (fun h => by rw [coinAt_locked _ (by decide)]; exact hbalA h) hsub a0 a1 a2 (by omega)
    (by omega) (fun h => absurd h ht0.2.2) ?_
  intro _ b' M' img' hL' hR' hW' hsz' hm' hn' hM'
  have hc0 : alD1c0 sevm = 9 := by unfold alD1c0; rw [ite_eq_right ht0.2.2]
  rw [hc0]
  rw [hc0] at hGb
  exact rx_al_back0X (P := P) hfork hstatic (.inr ⟨rfl, rfl, rfl⟩) hL' (hWc 4 (by decide)) hR' hW'
    hsz' hm' hXb (by rw [hAw]; exact hD1) hlt hslip hadd
    (by rw [al_stor3_tok, Stor.get_set_ne _ (by decide)]; exact hmint) hn' hM' (by omega)
    (by omega)

end Frame

end Blanc.Lift.Curve3Pool
