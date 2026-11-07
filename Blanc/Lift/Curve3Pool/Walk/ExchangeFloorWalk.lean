import Blanc.Lift.Curve3Pool.Walk.ExchangeFloorCores
import Blanc.Lift.Curve3Pool.Walk.ExchangeExactWalk
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityFloorWalk

/-!
# `exchange`, exact, at the true gas minimum

`rx_ex_frame_floor`: `rx_ex_frame_exact` for every residual gas `R ≥ 2201`, at the same cost `exExactCost`. The coin
calls are admitted at their floors: `4650` for the push, `5850` for the pull. The fee coin's two reads have a uniform
debit bound, so the existing cores take them at `8047 + 1000`. As in `remove_liquidity`, the floor that binds is the
lock's release (`rl_lock_sentry`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The push's raw tail's canonical successor. -/
noncomputable abbrev exPushTail (sevm : Sevm) (n : Devm) (M : Mem) (pN : Devm → List B256 → Mem → Devm) : Devm :=
  rawTailBaseNext sevm (exPushNext sevm n M pN) [] (exPushNext sevm n M pN).memory exPushSite

/-- The frame's end from the push's canonical base and memory: the raw tail, the event, the lock's release. -/
def ExEnd (sevm : Sevm) (n : Devm) (M : Mem) (pN : Devm → List B256 → Mem → Devm) (D : Devm) : Prop :=
  ∃ b' l S' M' G', Devm.EqModGas b' (exPushTail sevm n M pN) ∧
    D = St (afterSstore sevm (b'.addLog l) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])) S' M' G'

/-- A `balanceOf(self)` call site at `o`: its calldata and the memory's size. -/
structure ExBalWin (sevm : Sevm) (M : Mem) (o : Nat) : Prop where
  read : ((exBalIn M sevm o).read (o + 0x1c) 0x24).1 = balanceOfData sevm.currentTarget
  size : (exBalIn M sevm o).size = o + 0x40

theorem exBalWin_of {sevm : Sevm} {M : Mem} {img : Bytes} {o : Nat} (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size ≤ o)
    (hm : M.size % 32 = 0) (h32 : o % 32 = 0) : ExBalWin sevm M o := by
  constructor
  · exact (((hR.write hW _ _).write (hW.write _ _) _ _).read _ _).trans (bal_input _ _ o)
  · unfold exBalIn
    rw [Mem.size_write_word_aligned (Mem.size_write_word_mod hm) (by omega), Mem.size_write_word_aligned hm h32]
    omega

theorem rawTailCost_ge (n : Nat) : 261 ≤ rawTailCost n := by
  unfold rawTailCost rawJoinCost idCost
  split <;> omega

/-- What the frame still spends after the pull. -/
theorem exBackCost_ge (sevm : Sevm) (n : Devm) (M : Mem) (c0 : Nat) (σ : Stor) (B X : Nat → B256) (D : B256) (amp v : Nat)
    (pD : Devm → List B256 → Mem → Nat) (pN : Devm → List B256 → Mem → Devm) :
    11900 ≤ exBackCost sevm n M c0 σ B X D amp v pD pN := by
  have hcost : exBackCost sevm n M c0 σ B X D amp v pD pN =
      279 + c0 + 3540 + (3906 + costGetY sevm n amp (exI sevm).toNat (exJ sevm).toNat
        (exXw sevm X D).toNat (X 0).toNat (X 1).toNat (X 2).toNat) +
      (612 + sloadCost sevm (aBase sevm n) (Bytes.toB256 [0x02])) +
      exTailCost sevm (afterSload sevm (aBase sevm n) (Bytes.toB256 [0x02]))
        (exBackDyMem sevm M σ X D v) σ B D
        (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
        (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat))
        pD pN := rfl
  rw [hcost]
  unfold exTailCost exPushCost
  omega

/-- As its exact twin, at the floor. -/
theorem rx_ex_pushX_floor {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {dyOut : B256}
    {pD : Devm → List B256 → Mem → Nat} {pN : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hW'c : WClosed sevm W')
    (hj : (exJ sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xbc0)
    (hdata : Region img 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut))
    (hout : WordAt img 0x920 dyOut)
    (hpush : MutableFloorProfile sevm W W' (σ.get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ dyOut.toBytes) RawCallOk U 4650 0xb60 0x44 0xc00 pD pN)
    (hR0 : 2201 ≤ R) (hGb : R + exPushCost sevm n M pD pN + 2000 < 2 ^ 256)
    (k : ∀ D : Devm, ExLive sevm W' D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      D.gasLeft = R → ExEnd sevm n M pN D → ExPushWin sevm M dyOut → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] +
      Bytes.toB256 [32] + Bytes.toB256 [32]), Bytes.toB256 [10, 160]] M (R + exPushCost sevm n M pD pN))
      t_2b49_c1174 Q := by
  have hpin : Devm.EqModGas (exPushIn sevm b) (exPushIn sevm n) := Devm.EqModGas.afterSload sevm _ hn
  have e4 := Devm.EqModGas.sloadCost_congr sevm
    (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36])) hn
  obtain ⟨e5, hnx⟩ := hpush.congr [] (M.write 0xc0 (Bytes.toB256 [0]).toBytes) hpin
  have hT := rawTailCost_ge (min (exPushNext sevm n M pN).returnData.length 32)
  have hLk := sstoreCost_ge sevm (rawTailBaseNext sevm (exPushNext sevm n M pN) []
      (exPushNext sevm n M pN).memory exPushSite) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])
  have hWarm : gasWarmAccess = 100 := rfl
  refine rx_ex_push_coreF (R := R) (c := sstoreCost sevm (rawTailBaseNext sevm (exPushNext sevm n M pN) []
      (exPushNext sevm n M pN).memory exPushSite) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])) (Rf := R + 2232 + sstoreCost sevm (rawTailBaseNext sevm (exPushNext sevm n M pN) []
      (exPushNext sevm n M pN).memory exPushSite) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) +
      rawTailCost (min (exPushNext sevm n M pN).returnData.length 32))
    hfork hstatic hdepth hL hW'c hj hR hW hsz hdata hout hpush (by omega) (by decide)
    (by unfold exPushCost; rw [e5]; rw [e4]; omega) ?_ ?_ (rl_lock_sentry sevm _ _ _ hR0)
    hGb ?_
  · intro d hd
    have hdN : Devm.EqModGas d (exPushNext sevm n M pN) := hd.trans hnx
    rw [hdN.returnData]
  · intro d b' hd hb'
    have hdN : Devm.EqModGas d (exPushNext sevm n M pN) := hd.trans hnx
    have htail : Devm.EqModGas b' (rawTailBaseNext sevm (exPushNext sevm n M pN) []
        (exPushNext sevm n M pN).memory exPushSite) := by
      refine hb'.trans ?_
      rw [hdN.memory]
      exact rawTailBaseNext_congr sevm _ _ exPushSite hdN
    exact Devm.EqModGas.sstoreCost_congr sevm _ _ htail
  · rintro D hL' hg ⟨d, b', l, S', M', G', hd, hb', hD⟩ hw
    have hdN : Devm.EqModGas d (exPushNext sevm n M pN) := hd.trans hnx
    refine k D hL' hg ⟨b', l, S', M', G', hb'.trans ?_, hD⟩ hw
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ exPushSite hdN

/-- As its exact twin, at the floor. -/
theorem rx_ex_tail_floor {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W'' : Devm → Prop} {B X : Nat → B256} {D C dyOut dyFee : B256}
    {pD : Devm → List B256 → Mem → Nat} {pN : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa00)
    (hF : ExFrame img B X D C) (hout : WordAt img 0x920 dyOut) (hfee : WordAt img 0x940 dyFee)
    (hma : dyFee * σ.get adminFeeSlot / dyFee = σ.get adminFeeSlot ∨ dyFee = 0)
    (hmap : exAdm0 dyFee (σ.get adminFeeSlot) * exR0 / exAdm0 dyFee (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 dyFee (σ.get adminFeeSlot) = 0)
    (hbi : ¬ B (exI sevm).toNat + D < B (exI sevm).toNat)
    (hbj1 : ¬ B (exJ sevm).toNat < dyOut)
    (hbj2 : ¬ B (exJ sevm).toNat - dyOut <
      exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))
    (hW''c : WClosed sevm W'')
    (hpush : MutableFloorProfile sevm W W'' (σ.get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ dyOut.toBytes) RawCallOk U 4650 0xb60 0x44 0xc00 pD pN)
    (hR0 : 2201 ≤ R)
    (hGb : R + exTailCost sevm n M σ B D dyFee dyOut pD pN + 2000 < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D' (exFinal σ sevm (exVi sevm B D) (exVj sevm σ B dyFee dyOut)) →
      D'.gasLeft = R → ExEnd sevm (exTailN2 sevm n M σ B D dyFee dyOut) (exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut) pN D' →
      ExPushWin sevm (exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut) dyOut → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + exTailCost sevm n M σ B D dyFee dyOut pD pN))
      t_296f_c1174 Q := by
  have e3 : exStoreCost sevm b (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)) =
      exStoreCost sevm n (exVi sevm B D) (exVj sevm σ B dyFee dyOut) := exStoreCost_congr sevm hn _ _
  have hPc : 2340 ≤ exPushCost sevm (exTailN2 sevm n M σ B D dyFee dyOut)
      (exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut) pD pN := by unfold exPushCost; omega
  refine rx_ex_store_coreF (R := R + exPushCost sevm (exTailN2 sevm n M σ B D dyFee dyOut)
      (exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut) pD pN) hfork hstatic hdepth hL hi hj hR hW hsz hF hout hfee hma
    hmap hbi hbj1 hbj2 (by rw [e3]; unfold exTailCost; omega) (by omega) (by omega) ?_
  intro b5 M5 img5 g5 hL5 hR5 hW5 hsz5 hdata5 hout5 hgx5 bI1 hcan1 hcan2 hM5
  have hN1 : Devm.EqModGas bI1 (exTailN1 sevm n M σ B D dyFee dyOut) :=
    hcan1.trans (identityCallNext_congr sevm exStoreS1 _ _ _ _ _
      (exStoreBase_congr sevm hn (exVi sevm B D) (exVj sevm σ B dyFee dyOut)))
  have hN2 : Devm.EqModGas b5 (exTailN2 sevm n M σ B D dyFee dyOut) :=
    hcan2.trans (identityCallNext_congr sevm exStoreS2 _ _ _ _ _ hN1)
  have hcj : ((σ.set (balancesBase + exI sevm) (B (exI sevm).toNat + D)).set
      (balancesBase + exJ sevm) (B (exJ sevm).toNat - dyOut -
        exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))).get (coinsBase + exJ sevm) =
      σ.get (coinsBase + exJ sevm) := by
    have hiN : balancesBase + exI sevm = balancesBase + Nat.toB256 (exI sevm).toNat := by
      rw [toB256_toNat]
    have hjN : balancesBase + exJ sevm = balancesBase + Nat.toB256 (exJ sevm).toNat := by
      rw [toB256_toNat]
    have hcN : coinsBase + exJ sevm = coinsBase + Nat.toB256 (exJ sevm).toNat := by
      rw [toB256_toNat]
    rw [Stor.get_set_ne _ (by rw [hjN, hcN]; exact bal_ne_coin hj hj),
      Stor.get_set_ne _ (by rw [hiN, hcN]; exact bal_ne_coin hi hj)]
  have hg5 : g5 = R + exPushCost sevm (exTailN2 sevm n M σ B D dyFee dyOut)
      (exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut) pD pN := by
    rw [e3] at hgx5; unfold exTailCost at hgx5; omega
  rw [hg5, hM5]
  rw [hM5] at hR5 hW5 hsz5
  exact rx_ex_pushX_floor hfork hstatic hdepth hL5 hN2 hW''c hj hR5 hW5 hsz5 hdata5 hout5
    (by rw [hcj]; exact hpush) hR0 (by unfold exTailCost at hGb; omega) k

/-- As its exact twin, at the floor. -/
theorem rx_ex_back_floor {sevm : Sevm} {b n : Devm} {σ : Stor} {s0 : State} {R U amp v : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W W'' : Devm → Prop} {B X : Nat → B256}
    {D C : B256} {s c0 : Nat} {pD : Devm → List B256 → Mem → Nat}
    {pN : Devm → List B256 → Mem → Devm} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n) (ha : Abstracts σ s0)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0x6e0 ∧ c0 = 26) ∨ (s = 0x7a0 ∧ c0 = 6)) (hF : ExFrame img B X D C)
    (hmx : D * exRate (exI sevm).toNat / D = exRate (exI sevm).toNat ∨ D = 0)
    (hax : ¬ X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0 < X (exI sevm).toNat)
    (hA : aChk s0 sevm.benvStat.time.toNat = some amp)
    (hres : getYChk amp ⟨(exI sevm).toNat, hi⟩ ⟨(exJ sevm).toNat, hj⟩
      (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0).toNat
      (V3.mk (X 0).toNat (X 1).toNat (X 2).toNat).get = some v)
    (hy1 : ¬ X (exJ sevm).toNat < Nat.toB256 v)
    (hy2 : ¬ X (exJ sevm).toNat - Nat.toB256 v < Bytes.toB256 [1])
    (hmf : exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) * σ.get feeSlot /
      exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) = σ.get feeSlot ∨
      exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) = 0)
    (hsf : ¬ exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) <
      exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
    (hmo : (exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) * exR0 /
        (exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) -
          exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) = exR0 ∨
      exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = 0)
    (hmin : ¬ exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
      (exRate (exJ sevm).toNat) < exMinDy sevm)
    (hma : exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) * σ.get adminFeeSlot /
        exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = σ.get adminFeeSlot ∨
      exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = 0)
    (hmap : exAdm0 (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
        (σ.get adminFeeSlot) * exR0 /
        exAdm0 (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
        (σ.get adminFeeSlot) = 0)
    (hbi : ¬ B (exI sevm).toNat + D < B (exI sevm).toNat)
    (hbj1 : ¬ B (exJ sevm).toNat < exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
      (exRate (exJ sevm).toNat))
    (hbj2 : ¬ B (exJ sevm).toNat - exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
        (exRate (exJ sevm).toNat) <
      exAdm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) (σ.get adminFeeSlot)
        (exRate (exJ sevm).toNat))
    (hW''c : WClosed sevm W'')
    (hpush : MutableFloorProfile sevm W W'' (σ.get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v)
        (σ.get feeSlot) (exRate (exJ sevm).toNat)).toBytes) RawCallOk U 4650 0xb60 0x44 0xc00 pD pN)
    (hR0 : 2201 ≤ R)
    (hGb : R + exBackCost sevm n M c0 σ B X D amp v pD pN + 2000 < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D' (exFinal σ sevm (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
        (exRate (exJ sevm).toNat) -
        exAdm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) (σ.get adminFeeSlot)
          (exRate (exJ sevm).toNat))) → D'.gasLeft = R →
      ExEnd sevm (exTailN2 sevm (afterSload sevm (aBase sevm n) (Bytes.toB256 [0x02])) (exBackDyMem sevm M σ X D v) σ B D
          (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat)))
        (exStoreI2 (exBackDyMem sevm M σ X D v) sevm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (σ.get adminFeeSlot) (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat))) pN D' →
      ExPushWin sevm (exStoreI2 (exBackDyMem sevm M σ X D v) sevm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (σ.get adminFeeSlot) (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat)))
        (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat)) → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + exBackCost sevm n M c0 σ B X D amp v pD pN))
      t_26c9_c13 Q := by
  have hc0 : c0 ≤ 26 := by omega
  have hT : 3565 ≤ exTailCost sevm (afterSload sevm (aBase sevm n) (Bytes.toB256 [0x02]))
      (exBackDyMem sevm M σ X D v) σ B D
      (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
      (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat))
      pD pN := by unfold exTailCost exPushCost; omega
  have hcost : exBackCost sevm n M c0 σ B X D amp v pD pN =
      279 + c0 + 3540 + (3906 + costGetY sevm n amp (exI sevm).toNat (exJ sevm).toNat
        (exXw sevm X D).toNat (X 0).toNat (X 1).toNat (X 2).toNat) +
      (612 + sloadCost sevm (aBase sevm n) (Bytes.toB256 [0x02])) +
      exTailCost sevm (afterSload sevm (aBase sevm n) (Bytes.toB256 [0x02]))
        (exBackDyMem sevm M σ X D v) σ B D
        (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
        (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat))
        pD pN := rfl
  have e1 : costGetY sevm b amp (exI sevm).toNat (exJ sevm).toNat
      (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0).toNat (X 0).toNat (X 1).toNat
      (X 2).toNat = costGetY sevm n amp (exI sevm).toNat (exJ sevm).toNat (exXw sevm X D).toNat
      (X 0).toNat (X 1).toNat (X 2).toNat :=
    costGetY_congr sevm hn amp _ _ _ _ _ _
  -- `x`
  refine rx_ex_x_core (R := 0) hi hR hW hsz hs hF hmx hax (by omega) ?_
  intro M1 img1 g1 hR1 hW1 hsz1 hF1 hx1 hc1 _ hg1' hgx1 hM1
  rw [show Bytes.toB256 [1, 0x40] = Nat.toB256 (0x140 + 32 * 0) by decide] at hc1
  obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 67 * 52 + 56 := ⟨g1 - 3540, by omega⟩
  have hw : (fun o => Bytes.toB256 (img1.sliceD o 32 0)) = exSaveW M (exXw sevm X D) := by
    funext o
    unfold exSaveW memWord exXMem
    rw [← hM1, hR1.read]
  -- the save
  rw [ex_save_first, show ([] : List B256) = [] from rfl]
  refine rx_ex_saveFrom_core (fun o => Bytes.toB256 (img1.sliceD o 32 0)) 52 (n := 0) (S := [])
    rfl hR1 hW1 hsz1 hc1 (fun m _ _ => WordAt.self _ _) (by simp only [List.length_nil]; omega) ?_
  intro M2 img2 hR2 hW2 hsz2 hk2 hM2
  rw [List.append_nil]
  -- `get_y` and the restore
  refine rx_ex_y_core (R := 0) hfork hL ha hA hi hj hres hR2 hW2 hsz2
    (hF1.mono fun o v hv ho => hk2 o v hv (by omega)) (hk2 _ _ hx1 (by omega)) (by omega) ?_
  intro b3 M3 img3 g3 hL3 hR3 hW3 hsz3 hm3 hy3 _ hg3' hgx3 hb3 hM3
  have hF3 : ExFrame img3 B X D C := ExFrame.of_restore hF1 fun m hm => hm3 m (by omega)
  have hn3 : Devm.EqModGas b3 (aBase sevm n) := by rw [hb3]; exact aBase_congr sevm hn
  have e2 := Devm.EqModGas.sloadCost_congr sevm (Bytes.toB256 [0x02]) hn3
  -- `dy`
  refine rx_ex_dy_core (R := 0) hfork hL3 hj hR3 hW3 hsz3 hF3 hy3 hy1 hy2 hmf hsf hmo hmin
    (by omega) ?_
  intro b4 M4 img4 g4 hL4 hR4 hW4 hsz4 hF4 hout4 hfee4 _ hg4' hgx4 hb4 hM4
  have hn4 : Devm.EqModGas b4 (afterSload sevm (aBase sevm n) (Bytes.toB256 [0x02])) := by
    rw [hb4]; exact Devm.EqModGas.afterSload sevm _ hn3
  have hM4' : M4 = exBackDyMem sevm M σ X D v := by
    rw [hM4, hM3, hM2, hM1, hw]
    dsimp only [exBackDyMem, exBackYMem, exXMem]
  rw [hM4'] at hR4 hW4 hsz4
  have hg4 : g4 = R + exTailCost sevm (afterSload sevm (aBase sevm n) (Bytes.toB256 [0x02]))
      (exBackDyMem sevm M σ X D v) σ B D
      (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
      (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat))
      pD pN := by omega
  rw [hg4, hM4']
  exact rx_ex_tail_floor hfork hstatic hdepth hL4 hn4 hi hj hR4 hW4 hsz4 hF4 hout4 hfee4 hma hmap
    hbi hbj1 hbj2 hW''c hpush hR0 (by omega) k

/-- As its exact twin, at the floor. -/
theorem rx_ex_pull_floor {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C : B256} {s c0 : Nat}
    {plD : Devm → List B256 → Mem → Nat} {plN : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0x3c0 ∧ c0 = 31) ∨ (s = 0x460 ∧ c0 = 15)) (hF : ExFrame img B X D C)
    (hpull : MutableFloorProfile sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 5850 0x600 0x64 0x6c0 plD plN)
    (hR0 : 5850 ≤ R) (hGb : R + exPullCost sevm n M c0 plD plN + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x6e0 → ExFrame img' B X D C →
      Devm.EqModGas b' (exPullTail sevm n M plN) → M' = exPullMem sevm n M plN → ExPullWin sevm M →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_2666_c12 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + exPullCost sevm n M c0 plD plN)) t_2517_c11 Q := by
  refine rx_ex_pull_coreF (Rf := R + rawTailCost (min (exPullNext sevm n M plN).returnData.length 32))
    (Db := plD (exPullN2 sevm n M) [] (exPullI2 M sevm)) hfork hdepth hL hW'c hR hW hsz hs hF hpull
    (by omega) (by decide)
    (fun bI1 bI h1 h2 => (hpull.congr [] _ (h2.trans (identityCallNext_congr sevm exPullS2 _ _ _ _ _
      (h1.trans (identityCallNext_congr sevm exPullS1 _ _ _ _ _ hn))))).1)
    (by unfold exPullCost; omega) hGb ?_
  intro b' M' img' g h1 h2 h3 h4 h5 bI1 bI d hc1 hc2 hE hg hcT hM' hWin
  have hN1 : Devm.EqModGas bI1 (exPullN1 sevm n M) :=
    hc1.trans (identityCallNext_congr sevm exPullS1 _ _ _ _ _ hn)
  have hN2 : Devm.EqModGas bI (exPullN2 sevm n M) :=
    hc2.trans (identityCallNext_congr sevm exPullS2 _ _ _ _ _ hN1)
  obtain ⟨e5, hnx⟩ := hpull.congr [] (exPullI2 M sevm) hN2
  obtain ⟨hEg, hEn⟩ := hE
  have hEg' : R + exPullCost sevm n M c0 plD plN - (575 + c0) =
      d.gasLeft + plD bI [] (exPullI2 M sevm) := hEg
  have hdN : Devm.EqModGas d (exPullNext sevm n M plN) := hEn.trans hnx
  have e6 : min d.returnData.length 32 = min (exPullNext sevm n M plN).returnData.length 32 := by
    rw [hdN.returnData]
  have hgR : g = R := by
    rw [e6] at hg
    unfold exPullCost at hEg' hGb
    omega
  subst hgR
  refine k b' M' img' h1 h2 h3 h4 h5 ?_ ?_ hWin
  · refine hcT.trans ?_
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ exPullSite hdN
  · rw [hM', hdN.memory, e6]; rfl

/-- As its exact twin, at the floor. -/
theorem rx_ex_bal1_floor {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C B1 : B256}
    {bD : Devm → List B256 → Mem → Nat} {bN : Devm → List B256 → Mem → Devm}
    (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0)
    (hF : ExFrame img B X D C)
    (hbal : StaticWordFloorProfile sevm W W C (balanceOfData sevm.currentTarget) B1 U 1000 0x3dc 0x24 0x440
      bD bN)
    (hle : ∀ b S M, W b → (M.read (0x3dc : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
      bD b S M ≤ 8047)
    (hR0 : 10100 ≤ R) (hGb : R + (97 + bD n [] (exBalIn M sevm 0x3c0)) < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x460 → ExFrame img' B X B1 C →
      Devm.EqModGas b' (exBal1Next sevm n M bN) → M' = exBal1Mem sevm n M B1 bN → ExBalWin sevm M 0x3c0 →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_2517_c11 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + (97 + bD n [] (exBalIn M sevm 0x3c0)))) t_24d8_c0 Q := by
  obtain ⟨e5, hnx⟩ := hbal.congr [] (exBalIn M sevm 0x3c0) hn
  refine rx_ex_bal1_core (R := 0) hL hR hW hsz hF (StaticWordFloorProfile.okE hbal hle) (by omega)
    (by omega) ?_
  intro b' M' img' g h1 h2 h3 h4 h5 _ _ hE hg hM'
  obtain ⟨hEg, hEn⟩ := hE
  have hEg' : R + (97 + bD n [] (exBalIn M sevm 0x3c0)) - 44 =
      b'.gasLeft + bD b [] (exBalIn M sevm 0x3c0) := hEg
  have hdN : Devm.EqModGas b' (exBal1Next sevm n M bN) := hEn.trans hnx
  have hgR : g = R := by omega
  subst hgR
  refine k b' M' img' h1 h2 h3 h4 h5 hdN ?_ (exBalWin_of hR hW (by rw [hsz]) (by rw [hsz]) (by decide))
  rw [hM', hdN.returnData]; rfl

/-- As its exact twin, at the floor. -/
theorem rx_ex_bal2_floor {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {C B1 B2 : B256}
    {bD : Devm → List B256 → Mem → Nat} {bN : Devm → List B256 → Mem → Devm}
    (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x6e0)
    (hF : ExFrame img B X B1 C)
    (hbal : StaticWordFloorProfile sevm W W C (balanceOfData sevm.currentTarget) B2 U 1000 0x71c 0x24 0x780
      bD bN)
    (hle : ∀ b S M, W b → (M.read (0x71c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
      bD b S M ≤ 8047) (hsub : ¬ B2 < B1)
    (hR0 : 10100 ≤ R) (hGb : R + (151 + bD n [] (exBalIn M sevm 0x700)) < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x7a0 → ExFrame img' B X (B2 - B1) C →
      Devm.EqModGas b' (exBal2Next sevm n M bN) → M' = exBal2Mem sevm n M B1 B2 bN → ExBalWin sevm M 0x700 →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + (151 + bD n [] (exBalIn M sevm 0x700)))) t_2672_c12 Q := by
  obtain ⟨e5, hnx⟩ := hbal.congr [] (exBalIn M sevm 0x700) hn
  refine rx_ex_bal2_core (R := 0) hL hR hW hsz hF (StaticWordFloorProfile.okE hbal hle) hsub (by omega)
    (by omega) ?_
  intro b' M' img' g h1 h2 h3 h4 h5 _ _ hE hg hM'
  obtain ⟨hEg, hEn⟩ := hE
  have hEg' : R + (151 + bD n [] (exBalIn M sevm 0x700)) - 47 =
      b'.gasLeft + bD b [] (exBalIn M sevm 0x700) := hEg
  have hdN : Devm.EqModGas b' (exBal2Next sevm n M bN) := hEn.trans hnx
  have hgR : g = R := by omega
  subst hgR
  refine k b' M' img' h1 h2 h3 h4 h5 hdN ?_ (exBalWin_of hR hW (by rw [hsz]; decide) (by rw [hsz]) (by decide))
  rw [hM', hdN.returnData]; rfl

/-- As its exact twin, at the floor. -/
theorem rx_ex_head_floor {sevm : Sevm} {pre : Devm} {R : Nat} {Q : Outcome → Prop}
    {W : Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hWb : W pre)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3) (hR0 : 2301 ≤ R)
    (k : ∀ img1 : Bytes,
      ExBase sevm pre (exPreBase sevm pre) ((pre.getStor sevm.currentTarget).set lockSlot 1) →
      W (exPreBase sevm pre) →
      Mem.Reads (exPreMem (exM0 sevm) (pre.getStor sevm.currentTarget)) img1 →
      Mem.Wf (exPreMem (exM0 sevm) (pre.getStor sevm.currentTarget)) →
      (exPreMem (exM0 sevm) (pre.getStor sevm.currentTarget)).size = 0x2e0 →
      SFunc.RunEx cert.prog sevm (St (exPreBase sevm pre)
        [balAt (pre.getStor sevm.currentTarget) 0, balAt (pre.getStor sevm.currentTarget) 1,
          balAt (pre.getStor sevm.currentTarget) 2, exZ sevm 0x240, exZ sevm 0x220, exZ sevm 0x200,
          balAt (pre.getStor sevm.currentTarget) 2, balAt (pre.getStor sevm.currentTarget) 1,
          balAt (pre.getStor sevm.currentTarget) 0, exR1, exR1, exR0, Bytes.toB256 [2, 0]]
        (exPreMem (exM0 sevm) (pre.getStor sevm.currentTarget)) R)
        (pcCallTree 0x2452 0x03 0xa1 34 t_2458_c0) Q) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + 422 + (661 + exPreCost sevm pre)))
      t_0000_c0 Q := by
  rw [show R + 422 + (661 + exPreCost sevm pre) = (R + (661 + exPreCost sevm pre)) + 422 by omega]
  refine rx_dispatch_ex hlen hcd hsel ?_
  refine rx_ex_pre_coreF (b0 := pre) (σ := pre.getStor sevm.currentTarget) (R := R) hfork
    hstatic ⟨fun _ => rfl, rfl, rfl, hid.toH⟩ hWc hWb hlock hval hkill hi hj
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
    (vyMem_empty_size _) (vyImg_clamps _ _) (by omega) hR0 ?_
  intro b1 M1 img1 g1 z0 z1 z2 hB1 hW1 hR1 hWf1 hsz1 hgx1 hb1 hM1 hz0 hz1 hz2
  have hg : g1 = R := by omega
  rw [hg]; rw [hb1] at hB1 hW1 ⊢; rw [hM1] at hR1 hWf1 hsz1 ⊢; rw [hz0, hz1, hz2]
  exact k img1 hB1 hW1 hR1 hWf1 hsz1

/-- As its exact twin, at the floor. -/
theorem rx_ex_front_floor {sevm : Sevm} {pre : Devm} {R : Nat} {Q : Outcome → Prop}
    {W : Devm → Prop} {x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hWb : W pre)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hX : xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hR0 : 2201 ≤ R)
    (k : ∀ img2 : Bytes,
      ExBase sevm pre (exN2 sevm pre) ((pre.getStor sevm.currentTarget).set lockSlot 1) →
      W (exN2 sevm pre) → Mem.Reads (exM2 sevm pre x0 x1 x2) img2 →
      Mem.Wf (exM2 sevm pre x0 x1 x2) → (exM2 sevm pre x0 x1 x2).size = 0x3c0 →
      ExFrame img2 (exW3 (balAt (pre.getStor sevm.currentTarget) 0)
        (balAt (pre.getStor sevm.currentTarget) 1) (balAt (pre.getStor sevm.currentTarget) 2))
        (exW3 x0 x1 x2) (exDx sevm)
        (((pre.getStor sevm.currentTarget).set lockSlot 1).get (coinsBase + exI sevm)) →
      SFunc.RunEx cert.prog sevm (St (exN2 sevm pre) [Bytes.toB256 [0x25, 0x17],
        B256.eqCheck (B256.eqCheck (exI sevm) (Bytes.toB256 [2])) 0] (exM2 sevm pre x0 x1 x2) R)
        (.branchTo t_24d8_c0 11) Q) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + exHeadCost sevm pre)) t_0000_c0 Q := by
  rw [show R + exHeadCost sevm pre = (R + (1589 + sloadCost sevm (exPreBase sevm pre)
      (coinsBase + exI sevm))) + 422 + (661 + exPreCost sevm pre) by unfold exHeadCost; omega]
  refine rx_ex_head_floor hfork hstatic hlen hcd hsel hid hWc hWb hlock hval hkill hi hj
    (by omega) ?_
  intro img1 hB1 hW1 hR1 hWf1 hsz1
  refine rx_ex_mid_core (R := 0) hfork hB1 hWc hW1 hi hX hR1 hWf1 hsz1 (by omega) ?_
  intro b2 M2 img2 g2 x0' x1' x2' hxp hB2 hW2 hR2 hWf2 hsz2 hF2 _ hg2' hgx2 hb2 hM2
  obtain ⟨e0, e1, e2⟩ := V3.mk.inj hxp
  obtain rfl := B256.toNat_inj _ _ e0
  obtain rfl := B256.toNat_inj _ _ e1
  obtain rfl := B256.toNat_inj _ _ e2
  have hg : g2 = R := by omega
  have hb : b2 = exN2 sevm pre := hb2
  have hM : M2 = exM2 sevm pre x0 x1 x2 := hM2
  rw [hg]; rw [hb] at hB2 hW2 ⊢; rw [hM] at hR2 hWf2 hsz2 ⊢
  exact k img2 hB2 hW2 hR2 hWf2 hsz2 hF2

/-- As its exact twin, at the floor. -/
theorem rx_ex_nofee_floor {sevm : Sevm} {b : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C : B256}
    {plD : Devm → List B256 → Mem → Nat} {plN : Devm → List B256 → Mem → Devm}
    (hfee : exI sevm ≠ 2) (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0) (hF : ExFrame img B X D C)
    (hpull : MutableFloorProfile sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 5850 0x600 0x64 0x6c0 plD plN)
    (hR0 : 5850 ≤ R) (hGb : R + (29 + exPullCost sevm b M 31 plD plN) + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x6e0 → ExFrame img' B X D C →
      Devm.EqModGas b' (exPullTail sevm b M plN) → M' = exPullMem sevm b M plN → ExPullWin sevm M →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [Bytes.toB256 [0x25, 0x17],
        B256.eqCheck (B256.eqCheck (exI sevm) (Bytes.toB256 [2])) 0] M
        (R + (29 + exPullCost sevm b M 31 plD plN) + 10)) (.branchTo t_24d8_c0 11) Q := by
  xr (rx_branchTo_succ (exFeeTest_ne hfee) (g := t_2517_c11) rfl ·)
  rw [show R + (29 + exPullCost sevm b M 31 plD plN) = (R + 29) + exPullCost sevm b M 31 plD plN by
    omega]
  refine rx_ex_pull_floor hfork hdepth hL (Devm.EqModGas.refl _) hW'c hR hW hsz (.inl ⟨rfl, rfl⟩) hF
    hpull (by omega) (by omega) ?_
  intro b' M' img' h1 h2 h3 h4 h5 hn' hM' hWin
  exact rx_ex_test2_ne hfee (k b' M' img' h1 h2 h3 h4 h5 hn' hM' hWin)

/-- As its exact twin, at the floor. -/
theorem rx_ex_fee_floor {sevm : Sevm} {b : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C B1 B2 : B256}
    {bD1 bD2 plD : Devm → List B256 → Mem → Nat} {bN1 bN2 plN : Devm → List B256 → Mem → Devm}
    (hfee : exI sevm = 2) (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0) (hF : ExFrame img B X D C)
    (hb1 : StaticWordFloorProfile sevm W W C (balanceOfData sevm.currentTarget) B1 U 1000 0x3dc 0x24 0x440
      bD1 bN1)
    (hl1 : ∀ b S M, W b → (M.read (0x3dc : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
      bD1 b S M ≤ 8047)
    (hb2 : StaticWordFloorProfile sevm W' W' C (balanceOfData sevm.currentTarget) B2 U 1000 0x71c 0x24 0x780
      bD2 bN2)
    (hl2 : ∀ b S M, W' b → (M.read (0x71c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
      bD2 b S M ≤ 8047) (hsub : ¬ B2 < B1)
    (hpull : MutableFloorProfile sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 5850 0x600 0x64 0x6c0 plD plN)
    (hR0 : 10100 ≤ R)
    (hGb : R + exFeeMidCost sevm b M B1 bD1 bN1 plD plN bD2 + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x7a0 → ExFrame img' B X (B2 - B1) C →
      Devm.EqModGas b' (exBal2Next sevm (exPullTail sevm (exBal1Next sevm b M bN1)
        (exBal1Mem sevm b M B1 bN1) plN)
        (exPullMem sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) bN2) →
      M' = exBal2Mem sevm (exPullTail sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN)
        (exPullMem sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) B1 B2 bN2 →
      ExBalWin sevm M 0x3c0 → ExPullWin sevm (exBal1Mem sevm b M B1 bN1) →
      ExBalWin sevm (exPullMem sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) 0x700 →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [Bytes.toB256 [0x25, 0x17],
        B256.eqCheck (B256.eqCheck (exI sevm) (Bytes.toB256 [2])) 0] M
        (R + exFeeMidCost sevm b M B1 bD1 bN1 plD plN bD2)) (.branchTo t_24d8_c0 11) Q := by
  unfold exFeeMidCost at hGb ⊢
  rw [show R + (10 + (97 + bD1 b [] (exBalIn M sevm 0x3c0)) +
      exPullCost sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) 15 plD plN + 29 +
      (151 + bD2 (exPullTail sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) []
        (exBalIn (exPullMem sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) sevm
          0x700))) =
      (R + (151 + bD2 (exPullTail sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) []
        (exBalIn (exPullMem sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) sevm
          0x700)) + 29 + exPullCost sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) 15
          plD plN + (97 + bD1 b [] (exBalIn M sevm 0x3c0))) + 10 by omega]
  xr (rx_branchTo_zero' (exFeeTest_eq hfee) ·)
  refine rx_ex_bal1_floor hL (Devm.EqModGas.refl _) hR hW hsz hF hb1 hl1 (by omega) (by omega) ?_
  intro b4 M4 img4 hL4 hR4 hW4 hsz4 hF4 hn4 hM4 hw1
  rw [hM4] at hR4 hW4 hsz4 ⊢
  refine rx_ex_pull_floor hfork hdepth hL4 hn4 hW'c hR4 hW4 hsz4 (.inr ⟨rfl, rfl⟩) hF4 hpull
    (by omega) (by omega) ?_
  intro b5 M5 img5 hL5 hR5 hW5 hsz5 hF5 hn5 hM5 hw2
  rw [hM5] at hR5 hW5 hsz5 ⊢
  refine rx_ex_test2_eq hfee ?_
  exact rx_ex_bal2_floor hL5 hn5 hR5 hW5 hsz5 hF5 hb2 hl2 hsub (by omega) (by omega)
    fun b' M' img' h1 h2 h3 h4 h5 h6 h7 hw3 => k b' M' img' h1 h2 h3 h4 h5 h6 h7 hw1 hw2 hw3

/-- The pull's base and memory on the way to `x`, and the credited amount and `x`'s memory charge, by path. -/
structure ExPath where
  n : Devm
  M : Mem
  c0 : Nat
  D : B256

/-- The stages' canonical path after the pull: the fee coin's second read, or the pull's raw tail. -/
noncomputable def exPath (sevm : Sevm) (pre : Devm) (P : ExchangeExactCalls) (x0 x1 x2 B1 B2 : B256) : ExPath :=
  open Classical in
  if exI sevm = 2 then
    ⟨exBal2Next sevm (exPullTail sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
      (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN)
      (exPullMem sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
        (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN) P.balN2,
    exBal2Mem sevm (exPullTail sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
      (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN)
      (exPullMem sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
        (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN) B1 B2 P.balN2,
    6, B2 - B1⟩
  else ⟨exPullTail sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.pullN,
    exPullMem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.pullN, 26, exDx sevm⟩

/-- The call sites before the back half, by path. -/
def ExFrontWins (sevm : Sevm) (pre : Devm) (P : ExchangeExactCalls) (x0 x1 x2 B1 : B256) : Prop :=
  (exI sevm = 2 → ExBalWin sevm (exM2 sevm pre x0 x1 x2) 0x3c0 ∧
    ExPullWin sevm (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) ∧
    ExBalWin sevm (exPullMem sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
      (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN) 0x700) ∧
  (exI sevm ≠ 2 → ExPullWin sevm (exM2 sevm pre x0 x1 x2))

/-- As its exact twin, at the floor. -/
theorem rx_ex_frame_floor {sevm : Sevm} {pre : Devm} {s0 : State} {R U amp v : Nat}
    {Q : Outcome → Prop} {W W' W'' : Devm → Prop} {x0 x1 x2 B1 B2 : B256}
    (P : ExchangeExactCalls) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s0)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hX : xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hbal : exI sevm = 2 →
      StaticWordFloorProfile sevm W W ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm))
        (balanceOfData sevm.currentTarget) B1 U 1000 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
      (∀ b S M, W b → (M.read (0x3dc : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
      P.balD1 b S M ≤ 8047) ∧
      StaticWordFloorProfile sevm W' W' ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm))
        (balanceOfData sevm.currentTarget) B2 U 1000 0x71c 0x24 0x780 P.balD2 P.balN2 ∧
      (∀ b S M, W' b → (M.read (0x71c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
      P.balD2 b S M ≤ 8047) ∧ ¬ B2 < B1)
    (hpull : MutableFloorProfile sevm W W' ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm))
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
        (exDx sevm).toBytes) RawCallOk U 5850 0x600 0x64 0x6c0 P.pullD P.pullN)
    (hmx : exCred sevm B1 B2 * exRate (exI sevm).toNat / exCred sevm B1 B2 =
      exRate (exI sevm).toNat ∨ exCred sevm B1 B2 = 0)
    (hax : ¬ exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat / exR0 <
      exW3 x0 x1 x2 (exI sevm).toNat)
    (hA : aChk s0 sevm.benvStat.time.toNat = some amp)
    (hres : getYChk amp ⟨(exI sevm).toNat, hi⟩ ⟨(exJ sevm).toNat, hj⟩
      (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat / exR0).toNat
      (V3.mk x0.toNat x1.toNat x2.toNat).get = some v)
    (hy1 : ¬ exW3 x0 x1 x2 (exJ sevm).toNat < Nat.toB256 v)
    (hy2 : ¬ exW3 x0 x1 x2 (exJ sevm).toNat - Nat.toB256 v < Bytes.toB256 [1])
    (hmf : exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) *
        (pre.getStor sevm.currentTarget).get feeSlot /
        exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) =
        (pre.getStor sevm.currentTarget).get feeSlot ∨
      exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) = 0)
    (hsf : ¬ exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) <
      exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
    (hmo : (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot)) * exR0 /
        (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
            ((pre.getStor sevm.currentTarget).get feeSlot)) = exR0 ∨
      exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) = 0)
    (hmin : ¬ exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
      ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) < exMinDy sevm)
    (hma : exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot) *
        (pre.getStor sevm.currentTarget).get adminFeeSlot /
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) =
        (pre.getStor sevm.currentTarget).get adminFeeSlot ∨
      exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot) = 0)
    (hmap : exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
        ((pre.getStor sevm.currentTarget).get adminFeeSlot) * exR0 /
        exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) = exR0 ∨
      exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
        ((pre.getStor sevm.currentTarget).get adminFeeSlot) = 0)
    (hbi : ¬ exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi⟩ + exCred sevm B1 B2 <
      exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi⟩)
    (hbj1 : ¬ exBal (pre.getStor sevm.currentTarget) ⟨(exJ sevm).toNat, hj⟩ <
      exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat))
    (hbj2 : ¬ exBal (pre.getStor sevm.currentTarget) ⟨(exJ sevm).toNat, hj⟩ -
        exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) <
      exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
        ((pre.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat))
    (hW''c : WClosed sevm W'')
    (hpush : MutableFloorProfile sevm W' W''
      ((pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat)
        (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)).toBytes)
      RawCallOk U 4650 0xb60 0x44 0xc00 P.pushD P.pushN)
    (hR0 : 2201 ≤ R)
    (hGb : R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D' (exFinal ((pre.getStor sevm.currentTarget).set lockSlot 1)
      sevm (exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi⟩ + exCred sevm B1 B2)
      (exBal (pre.getStor sevm.currentTarget) ⟨(exJ sevm).toNat, hj⟩ -
        exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) -
        exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat))) →
      D'.gasLeft = R →
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
        P.pushN D' →
      ExPushWin sevm (exStoreI2 (exBackDyMem sevm (exPath sevm pre P x0 x1 x2 B1 B2).M ((pre.getStor sevm.currentTarget).set lockSlot 1)
            (exW3 x0 x1 x2) (exPath sevm pre P x0 x1 x2 B1 B2).D v) sevm
          (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot)
          (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)))
        (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)) →
      ExFrontWins sevm pre P x0 x1 x2 B1 → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v))
      t_0000_c0 Q := by

  have ef : ((pre.getStor sevm.currentTarget).set lockSlot 1).get feeSlot =
      (pre.getStor sevm.currentTarget).get feeSlot := Stor.get_set_ne _ (by decide) _
  have eaf : ((pre.getStor sevm.currentTarget).set lockSlot 1).get adminFeeSlot =
      (pre.getStor sevm.currentTarget).get adminFeeSlot := Stor.get_set_ne _ (by decide) _
  have eci : ((pre.getStor sevm.currentTarget).set lockSlot 1).get (coinsBase + exI sevm) =
      (pre.getStor sevm.currentTarget).get (coinsBase + exI sevm) := Stor.get_set_ne _ (by
    rw [show coinsBase + exI sevm = coinsBase + Nat.toB256 (exI sevm).toNat by rw [toB256_toNat]]
    exact coin_ne_lock hi) _
  have ecj : ((pre.getStor sevm.currentTarget).set lockSlot 1).get (coinsBase + exJ sevm) =
      (pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm) := Stor.get_set_ne _ (by
    rw [show coinsBase + exJ sevm = coinsBase + Nat.toB256 (exJ sevm).toNat by rw [toB256_toNat]]
    exact coin_ne_lock hj) _
  have ha1 : Abstracts ((pre.getStor sevm.currentTarget).set lockSlot 1) s0 :=
    ha.of_lock fun x hx => Stor.get_set_ne _ (Ne.symm hx) _
  have hh : 2672 ≤ exHeadCost sevm pre := by unfold exHeadCost; omega
  by_cases hfee : exI sevm = 2
  · -- the fee coin
    obtain ⟨hb1, hl1, hb2, hl2, hsub⟩ := hbal hfee
    have hD : exCred sevm B1 B2 = B2 - B1 := ite_eq_left hfee
    rw [hD] at hmx hax hres hbi k
    have hc : exExactCost sevm pre P x0 x1 x2 B1 B2 amp v = exHeadCost sevm pre +
        (exFeeMidCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balD1 P.balN1 P.pullD
          P.pullN P.balD2 + exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v) := by
      unfold exExactCost; rw [ite_eq_left hfee]
    rw [hc] at hGb ⊢
    have hBk : 11900 ≤ exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v := exBackCost_ge ..
    rw [show R + (exHeadCost sevm pre + (exFeeMidCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2)
        B1 P.balD1 P.balN1 P.pullD P.pullN P.balD2 + exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v)) =
        (R + exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v +
          exFeeMidCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balD1 P.balN1 P.pullD
            P.pullN P.balD2) + exHeadCost sevm pre by omega]
    refine rx_ex_front_floor hfork hstatic hlen hcd hsel hid hWc hWb hlock hval hkill hi hj hX
      (by omega) ?_
    intro img2 hB2 hW2 hR2 hWf2 hsz2 hF2
    rw [eci] at hF2
    refine rx_ex_fee_floor hfee hfork hdepth ⟨hB2.stor, (hB2.id.toCovered hfork), hWc, hW2⟩ hW'c hR2 hWf2 hsz2 hF2 hb1 hl1
      hb2 hl2 hsub hpull (by omega) (by omega) ?_
    intro b7 M7 img7 hL7 hR7 hWf7 hsz7 hF7 hn7 hM7 hw1 hw2 hw3
    have hpath : exPath sevm pre P x0 x1 x2 B1 B2 = _ := ite_eq_left hfee
    rw [hpath] at k
    rw [hM7] at hR7 hWf7 hsz7 ⊢
    exact rx_ex_back_floor hfork hstatic hdepth hL7 hn7 ha1 hi hj hR7 hWf7 hsz7 (.inr ⟨rfl, rfl⟩) hF7
      hmx hax hA hres hy1 hy2 (by rw [ef]; exact hmf) (by rw [ef]; exact hsf) (by rw [ef]; exact hmo)
      (by rw [ef]; exact hmin) (by rw [ef, eaf]; exact hma) (by rw [ef, eaf]; exact hmap) hbi
      (by rw [ef]; exact hbj1) (by rw [ef, eaf]; exact hbj2) hW''c (by rw [ef, ecj]; exact hpush)
      hR0 (by unfold exFeeBackCost at hGb; omega)
      (by rw [ef, eaf]; exact fun D' a b c d => k D' a b c d ⟨fun _ => ⟨hw1, hw2, hw3⟩, fun h => absurd hfee h⟩)
  · -- another coin
    have hD : exCred sevm B1 B2 = exDx sevm := ite_eq_right hfee
    rw [hD] at hmx hax hres hbi k
    have hc : exExactCost sevm pre P x0 x1 x2 B1 B2 amp v = exHeadCost sevm pre +
        ((29 + exPullCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) 31 P.pullD P.pullN + 10) +
          exNoFeeBackCost sevm pre P x0 x1 x2 amp v) := by
      unfold exExactCost; rw [ite_eq_right hfee]
    rw [hc] at hGb ⊢
    have hBk : 11900 ≤ exNoFeeBackCost sevm pre P x0 x1 x2 amp v := exBackCost_ge ..
    rw [show R + (exHeadCost sevm pre + ((29 + exPullCost sevm (exN2 sevm pre)
        (exM2 sevm pre x0 x1 x2) 31 P.pullD P.pullN + 10) + exNoFeeBackCost sevm pre P x0 x1 x2 amp v)) =
        (R + exNoFeeBackCost sevm pre P x0 x1 x2 amp v + (29 + exPullCost sevm (exN2 sevm pre)
          (exM2 sevm pre x0 x1 x2) 31 P.pullD P.pullN) + 10) + exHeadCost sevm pre by omega]
    refine rx_ex_front_floor hfork hstatic hlen hcd hsel hid hWc hWb hlock hval hkill hi hj hX
      (by omega) ?_
    intro img2 hB2 hW2 hR2 hWf2 hsz2 hF2
    rw [eci] at hF2
    refine rx_ex_nofee_floor hfee hfork hdepth ⟨hB2.stor, (hB2.id.toCovered hfork), hWc, hW2⟩ hW'c hR2 hWf2 hsz2 hF2
      hpull (by omega) (by omega) ?_
    intro b5 M5 img5 hL5 hR5 hWf5 hsz5 hF5 hn5 hM5 hw1
    have hpath : exPath sevm pre P x0 x1 x2 B1 B2 = _ := ite_eq_right hfee
    rw [hpath] at k
    rw [hM5] at hR5 hWf5 hsz5 ⊢
    exact rx_ex_back_floor hfork hstatic hdepth hL5 hn5 ha1 hi hj hR5 hWf5 hsz5 (.inl ⟨rfl, rfl⟩) hF5
      hmx hax hA hres hy1 hy2 (by rw [ef]; exact hmf) (by rw [ef]; exact hsf) (by rw [ef]; exact hmo)
      (by rw [ef]; exact hmin) (by rw [ef, eaf]; exact hma) (by rw [ef, eaf]; exact hmap) hbi
      (by rw [ef]; exact hbj1) (by rw [ef, eaf]; exact hbj2) hW''c (by rw [ef, ecj]; exact hpush)
      hR0 (by unfold exNoFeeBackCost at hGb; omega)
      (by rw [ef, eaf]; exact fun D' a b c d => k D' a b c d ⟨fun h => absurd h hfee, fun _ => hw1⟩)

end Blanc.Lift.Curve3Pool
