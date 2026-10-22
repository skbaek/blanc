import Blanc.Lift.Curve3Pool.ExchangeExactSchedule

/-!
# `exchange`, exact: the byte-level walk

The exact walk composes the stage cores (`rx_ex_pre_core`, `rx_ex_mid_core`,
`rx_ex_bal1_core`/`rx_ex_bal2_core`, `rx_ex_pull_core`, `rx_ex_x_core`, `rx_ex_saveFrom_core`,
`rx_ex_y_core`, `rx_ex_dy_core`, `rx_ex_store_core`, `rx_ex_push_core`) at the exact profiles'
relation `ExactE`. Each stage hands on its actual base, equal modulo gas to the schedule's
canonical one, and its literal memory; the stage charges and the profiles' debits agree there by
congruence, so the walk from `R + cost` ends with exactly `R`, the cost a function of the
canonical schedule only.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-! ## Charge congruences of the stores stage -/

theorem exStoreBase_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') (vi vj : B256) :
    Devm.EqModGas (exStoreBase sevm b vi vj) (exStoreBase sevm b' vi vj) :=
  Devm.EqModGas.afterSstore sevm _ _ (Devm.EqModGas.afterSstore sevm _ _
    (Devm.EqModGas.afterSload sevm _ h))

theorem exStoreCost_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') (vi vj : B256) :
    exStoreCost sevm b vi vj = exStoreCost sevm b' vi vj := by
  have h1 := Devm.EqModGas.afterSload sevm (Bytes.toB256 [3]) h
  have h2 := Devm.EqModGas.afterSstore sevm (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4]))
    vi h1
  unfold exStoreCost
  rw [Devm.EqModGas.sloadCost_congr sevm _ h, Devm.EqModGas.sstoreCost_congr sevm _ _ h1,
    Devm.EqModGas.sstoreCost_congr sevm _ _ h2]

/-! ## The canonical schedule after the pull -/

/-- `x`, as the walk computes it: `xp[i] + dx_w_fee * rates[i] / PRECISION`. -/
abbrev exXw (sevm : Sevm) (X : Nat → B256) (D : B256) : B256 :=
  X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0

/-- The memory `x` leaves. -/
def exXMem (M : Mem) (xw : B256) : Mem :=
  (M.write 0x7a0 xw.toBytes).write 0x7e0 (Bytes.toB256 [1, 0x40]).toBytes

/-- The words the frame save pushes: the words of `x`'s memory. -/
def exSaveW (M : Mem) (xw : B256) : Nat → B256 := fun o => memWord (exXMem M xw) o

/-- The push's input base: `coins[j]` loaded at the stores' last identity successor. -/
abbrev exPushIn (sevm : Sevm) (n : Devm) : Devm :=
  afterSload sevm n (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))

/-- The push call's canonical successor. -/
def exPushNext (sevm : Sevm) (n : Devm) (M : Mem) (pN : Devm → List B256 → Mem → Devm) : Devm :=
  pN (exPushIn sevm n) [] (M.write 0xc0 (Bytes.toB256 [0]).toBytes)

/-- **The exact charge of the push, the event and the lock**: `2340` fixed (including `LOG2`),
the `coins[j]` load, the profile's debit, the raw tail at the reply's actual length, and the lock
reset at the raw tail's canonical successor. -/
def exPushCost (sevm : Sevm) (n : Devm) (M : Mem) (pD : Devm → List B256 → Mem → Nat)
    (pN : Devm → List B256 → Mem → Devm) : Nat :=
  2340 + sloadCost sevm n (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36])) +
    pD (exPushIn sevm n) [] (M.write 0xc0 (Bytes.toB256 [0]).toBytes) +
    rawTailCost (min (exPushNext sevm n M pN).returnData.length 32) +
    sstoreCost sevm (rawTailBaseNext sevm (exPushNext sevm n M pN) []
      (exPushNext sevm n M pN).memory exPushSite) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])

/-- The values the stores write: `balances[i] + dx`, `balances[j] - dy - admin share`. -/
abbrev exVi (sevm : Sevm) (B : Nat → B256) (D : B256) : B256 := B (exI sevm).toNat + D

abbrev exVj (sevm : Sevm) (σ : Stor) (B : Nat → B256) (dyFee dyOut : B256) : B256 :=
  B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)

/-- The stores' first payload identity successor. -/
def exTailN1 (sevm : Sevm) (n : Devm) (M : Mem) (σ : Stor) (B : Nat → B256) (D dyFee dyOut : B256) :
    Devm :=
  identityCallNext sevm (exStoreBase sevm n (exVi sevm B D) (exVj sevm σ B dyFee dyOut))
    exStoreS1 (exStoreM1 M sevm dyFee (σ.get adminFeeSlot))
    (Bytes.toB256 [10, 64] + Bytes.toB256 [32]) (Bytes.toB256 [4])
    (Bytes.toB256 [10, 160] + Bytes.toB256 [0] + Bytes.toB256 [32]) (Bytes.toB256 [4])

/-- The stores' second payload identity successor. -/
def exTailN2 (sevm : Sevm) (n : Devm) (M : Mem) (σ : Stor) (B : Nat → B256) (D dyFee dyOut : B256) :
    Devm :=
  identityCallNext sevm (exTailN1 sevm n M σ B D dyFee dyOut) exStoreS2
    (exStoreM2 M sevm dyFee (σ.get adminFeeSlot) dyOut)
    (Bytes.toB256 [10, 160]) (Bytes.toB256 [32] + exPushLen) (Bytes.toB256 [11, 64])
    (Bytes.toB256 [32] + exPushLen)

/-- **The exact charge of the stores and the push**: the stores (`1225` plus `exStoreCost`), then
`exPushCost` at the second identity successor and the payload memory. -/
def exTailCost (sevm : Sevm) (n : Devm) (M : Mem) (σ : Stor) (B : Nat → B256) (D dyFee dyOut : B256)
    (pD : Devm → List B256 → Mem → Nat) (pN : Devm → List B256 → Mem → Devm) : Nat :=
  1225 + exStoreCost sevm n (exVi sevm B D) (exVj sevm σ B dyFee dyOut) +
    exPushCost sevm (exTailN2 sevm n M σ B D dyFee dyOut)
      (exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut) pD pN

/-- `y` and the memory after `get_y` and the restore, from the memory at `x`'s entry. -/
def exBackYMem (sevm : Sevm) (M : Mem) (X : Nat → B256) (D : B256) (v : Nat) : Mem :=
  exYMem (saveMem (exXMem M (exXw sevm X D)) 0x7e0 (0x140 + 32 * 0) (52 + 1)) sevm (exXw sevm X D)
    (X 0) (X 1) (X 2) v (exSaveW M (exXw sevm X D))

/-- The memory `dy` leaves, from the memory at `x`'s entry. -/
def exBackDyMem (sevm : Sevm) (M : Mem) (σ : Stor) (X : Nat → B256) (D : B256) (v : Nat) : Mem :=
  exDyMem (exBackYMem sevm M X D v) (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
    (exRate (exJ sevm).toNat)

/-- **The exact charge after the pull**, read at the canonical schedule: `x` (`279 + c0`), the
save (`3540`), `get_y` (`3906` plus `costGetY`), `dy` (`612` plus the `fee` load), then the stores
and the push (`exTailCost`). -/
def exBackCost (sevm : Sevm) (n : Devm) (M : Mem) (c0 : Nat) (σ : Stor) (B X : Nat → B256)
    (D : B256) (amp v : Nat) (pD : Devm → List B256 → Mem → Nat)
    (pN : Devm → List B256 → Mem → Devm) : Nat :=
  279 + c0 + 3540 + (3906 + costGetY sevm n amp (exI sevm).toNat (exJ sevm).toNat
      (exXw sevm X D).toNat (X 0).toNat (X 1).toNat (X 2).toNat) +
    (612 + sloadCost sevm (aBase sevm n) (Bytes.toB256 [0x02])) +
    exTailCost sevm (afterSload sevm (aBase sevm n) (Bytes.toB256 [0x02]))
      (exBackDyMem sevm M σ X D v) σ B D
      (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
      (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat)) pD pN

/-- **The push, the event and the lock, exactly**: from an actual base `b` equal modulo gas to
the canonical `n`, at the literal memory `M`, from `R + exPushCost` to `STOP` with exactly `R`. -/
theorem rx_ex_pushX_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {dyOut : B256}
    {pD : Devm → List B256 → Mem → Nat} {pN : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hW'c : WClosed sevm W')
    (hj : (exJ sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xbc0)
    (hdata : Region img 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut))
    (hout : WordAt img 0x920 dyOut)
    (hpush : MutableCallProfile sevm W W' (σ.get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ dyOut.toBytes) RawCallOk U 0xb60 0x44 0xc00 pD pN)
    (hR0 : 30000 + U ≤ R) (hGb : R + exPushCost sevm n M pD pN + 2000 < 2 ^ 256)
    (k : ∀ D : Devm, ExLive sevm W' D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      D.gasLeft = R → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] +
      Bytes.toB256 [32] + Bytes.toB256 [32]), Bytes.toB256 [10, 160]] M (R + exPushCost sevm n M pD pN))
      t_2b49_c1174 Q := by
  have hpin : Devm.EqModGas (exPushIn sevm b) (exPushIn sevm n) := Devm.EqModGas.afterSload sevm _ hn
  have e4 := Devm.EqModGas.sloadCost_congr sevm
    (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36])) hn
  obtain ⟨e5, hnx⟩ := hpush.congr [] (M.write 0xc0 (Bytes.toB256 [0]).toBytes) hpin
  refine rx_ex_push_core hfork hstatic hdepth hL hW'c hj hR hW hsz hdata hout
    (MutableCallProfile.okE hpush) (by unfold exPushCost; omega) (by omega) ?_
  intro D' hLD d b' hE hcanT hgd
  obtain ⟨hEg, hEn⟩ := hE
  have hdN : Devm.EqModGas d (exPushNext sevm n M pN) := hEn.trans hnx
  have e6 : min d.returnData.length 32 = min (exPushNext sevm n M pN).returnData.length 32 := by
    rw [hdN.returnData]
  have htail : Devm.EqModGas b' (rawTailBaseNext sevm (exPushNext sevm n M pN) []
      (exPushNext sevm n M pN).memory exPushSite) := by
    refine hcanT.trans ?_
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ exPushSite hdN
  have e7 := Devm.EqModGas.sstoreCost_congr sevm (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])
    htail
  have hEg' : R + exPushCost sevm n M pD pN -
      (108 + sloadCost sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) =
      d.gasLeft + pD (exPushIn sevm b) [] (M.write 0xc0 (Bytes.toB256 [0]).toBytes) := hEg
  refine k D' hLD ?_
  rw [e6] at hgd
  unfold exPushCost at hEg' hGb
  omega

/-- **The stores and the push, exactly**: from an actual base `b` equal modulo gas to the canonical
`n`, at the literal memory `M`, the frame runs from `R + exTailCost` to `STOP` with exactly `R`. -/
theorem rx_ex_tail_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
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
    (hpush : MutableCallProfile sevm W W'' (σ.get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ dyOut.toBytes) RawCallOk U 0xb60 0x44 0xc00 pD pN)
    (hR0 : 60000 + U ≤ R)
    (hGb : R + exTailCost sevm n M σ B D dyFee dyOut pD pN + 2000 < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D' (exFinal σ sevm (exVi sevm B D) (exVj sevm σ B dyFee dyOut)) →
      D'.gasLeft = R → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + exTailCost sevm n M σ B D dyFee dyOut pD pN))
      t_296f_c1174 Q := by
  have e3 : exStoreCost sevm b (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)) =
      exStoreCost sevm n (exVi sevm B D) (exVj sevm σ B dyFee dyOut) := exStoreCost_congr sevm hn _ _
  refine rx_ex_store_core (R := 0) hfork hstatic hdepth hL hi hj hR hW hsz hF hout hfee hma
    hmap hbi hbj1 hbj2 (by unfold exTailCost; omega) (by omega) ?_
  intro b5 M5 img5 g5 hL5 hR5 hW5 hsz5 hdata5 hout5 _ hg5' hgx5 bI1 hcan1 hcan2 hM5
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
    unfold exTailCost at hgx5; omega
  rw [hg5, hM5]
  rw [hM5] at hR5 hW5 hsz5
  exact rx_ex_pushX_exact hfork hstatic hdepth hL5 hN2 hW''c hj hR5 hW5 hsz5 hdata5 hout5
    (by rw [hcj]; exact hpush) (by omega) (by unfold exTailCost at hGb; omega) k

/-- **`exchange` after the pull, exactly**: from an actual base `b` equal modulo gas to the
canonical `n`, at the literal memory `M`, the rest of the frame runs from
`R + exBackCost` to `STOP` with exactly `R` left. -/
theorem rx_ex_back_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {s0 : State} {R U amp v : Nat}
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
    (hpush : MutableCallProfile sevm W W'' (σ.get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v)
        (σ.get feeSlot) (exRate (exJ sevm).toNat)).toBytes) RawCallOk U 0xb60 0x44 0xc00 pD pN)
    (hR0 : 60000 + U ≤ R)
    (hGb : R + exBackCost sevm n M c0 σ B X D amp v pD pN + 2000 < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D' (exFinal σ sevm (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
        (exRate (exJ sevm).toNat) -
        exAdm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) (σ.get adminFeeSlot)
          (exRate (exJ sevm).toNat))) → D'.gasLeft = R → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + exBackCost sevm n M c0 σ B X D amp v pD pN))
      t_26c9_c13 Q := by
  have hc0 : c0 ≤ 26 := by omega
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
  exact rx_ex_tail_exact hfork hstatic hdepth hL4 hn4 hi hj hR4 hW4 hsz4 hF4 hout4 hfee4 hma hmap
    hbi hbj1 hbj2 hW''c hpush hR0 (by omega) k


/-! ## The pull and the fee coin's two reads -/

/-- The pull payload's first identity successor. -/
def exPullN1 (sevm : Sevm) (n : Devm) (M : Mem) : Devm :=
  identityCallNext sevm n exPullS1 (exPullM1 M) (Bytes.toB256 [4, 192] + Bytes.toB256 [32])
    (Bytes.toB256 [4]) (Bytes.toB256 [5, 32] + Bytes.toB256 [0] + Bytes.toB256 [32]) (Bytes.toB256 [4])

/-- The pull payload's second identity successor (the `transferFrom` call's input base). -/
def exPullN2 (sevm : Sevm) (n : Devm) (M : Mem) : Devm :=
  identityCallNext sevm (exPullN1 sevm n M) exPullS2 (exPullM2 M sevm) (Bytes.toB256 [5, 32])
    (Bytes.toB256 [32] + exPullLen) (Bytes.toB256 [5, 224]) (Bytes.toB256 [32] + exPullLen)

/-- The `transferFrom` call's canonical successor. -/
def exPullNext (sevm : Sevm) (n : Devm) (M : Mem) (plN : Devm → List B256 → Mem → Devm) : Devm :=
  plN (exPullN2 sevm n M) [] (exPullI2 M sevm)

/-- The pull's raw tail canonical successor. -/
def exPullTail (sevm : Sevm) (n : Devm) (M : Mem) (plN : Devm → List B256 → Mem → Devm) : Devm :=
  rawTailBaseNext sevm (exPullNext sevm n M plN) [] (exPullNext sevm n M plN).memory exPullSite

/-- The memory the pull's raw tail leaves. -/
def exPullMem (sevm : Sevm) (n : Devm) (M : Mem) (plN : Devm → List B256 → Mem → Devm) : Mem :=
  vyRawMem (exPullNext sevm n M plN).memory 0x6a0 0x460
    (min (exPullNext sevm n M plN).returnData.length 32)

/-- **The pull's exact charge**: `575 + c0` fixed (both payload identity copies included), the
profile's debit, and the raw tail at the reply's actual length. -/
def exPullCost (sevm : Sevm) (n : Devm) (M : Mem) (c0 : Nat) (plD : Devm → List B256 → Mem → Nat)
    (plN : Devm → List B256 → Mem → Devm) : Nat :=
  575 + c0 + plD (exPullN2 sevm n M) [] (exPullI2 M sevm) +
    rawTailCost (min (exPullNext sevm n M plN).returnData.length 32)

/-- **The pull, exactly**: from an actual base equal modulo gas to `n`, at the literal memory
`M`, from `R + exPullCost` to the second fee test with exactly `R`, at a base equal modulo gas
to `exPullTail` and the memory `exPullMem`. -/
theorem rx_ex_pull_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C : B256} {s c0 : Nat}
    {plD : Devm → List B256 → Mem → Nat} {plN : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0x3c0 ∧ c0 = 31) ∨ (s = 0x460 ∧ c0 = 15)) (hF : ExFrame img B X D C)
    (hpull : MutableCallProfile sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 0x600 0x64 0x6c0 plD plN)
    (hR0 : 4000 + U ≤ R) (hGb : R + exPullCost sevm n M c0 plD plN + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x6e0 → ExFrame img' B X D C →
      Devm.EqModGas b' (exPullTail sevm n M plN) → M' = exPullMem sevm n M plN →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_2666_c12 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + exPullCost sevm n M c0 plD plN)) t_2517_c11 Q := by
  refine rx_ex_pull_core (R := 0) hfork hdepth hL hW'c hR hW hsz hs hF (MutableCallProfile.okE hpull)
    (by unfold exPullCost; omega) (by omega) ?_
  intro b' M' img' g h1 h2 h3 h4 h5 _ _ bI1 bI d hc1 hc2 hE hg hcT hM'
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
  refine k b' M' img' h1 h2 h3 h4 h5 ?_ ?_
  · refine hcT.trans ?_
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ exPullSite hdN
  · rw [hM', hdN.memory, e6]; rfl

/-- The first `balanceOf(self)` call's canonical successor. -/
def exBal1Next (sevm : Sevm) (n : Devm) (M : Mem) (bN : Devm → List B256 → Mem → Devm) : Devm :=
  bN n [] (exBalIn M sevm 0x3c0)

/-- The memory after the first `balanceOf(self)` and its answer parked at `0x380`. -/
def exBal1Mem (sevm : Sevm) (n : Devm) (M : Mem) (B1 : B256)
    (bN : Devm → List B256 → Mem → Devm) : Mem :=
  (((exBalIn M sevm 0x3c0).extends [(0x3dc, 0x24), (0x440, 0x20)]).write 0x440
    ((exBal1Next sevm n M bN).returnData.take 0x20)).write 0x380 B1.toBytes

/-- **The first `balanceOf(self)`, exactly**: `97` fixed plus the profile's debit. -/
theorem rx_ex_bal1_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C B1 : B256}
    {bD : Devm → List B256 → Mem → Nat} {bN : Devm → List B256 → Mem → Devm}
    (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0)
    (hF : ExFrame img B X D C)
    (hbal : StaticWordCallProfile sevm W W C (balanceOfData sevm.currentTarget) B1 U 0x3dc 0x24 0x440
      bD bN)
    (hR0 : 1000 + U ≤ R) (hGb : R + (97 + bD n [] (exBalIn M sevm 0x3c0)) < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x460 → ExFrame img' B X B1 C →
      Devm.EqModGas b' (exBal1Next sevm n M bN) → M' = exBal1Mem sevm n M B1 bN →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_2517_c11 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + (97 + bD n [] (exBalIn M sevm 0x3c0)))) t_24d8_c0 Q := by
  obtain ⟨e5, hnx⟩ := hbal.congr [] (exBalIn M sevm 0x3c0) hn
  refine rx_ex_bal1_core (R := 0) hL hR hW hsz hF (StaticWordCallProfile.okE hbal) (by omega)
    (by omega) ?_
  intro b' M' img' g h1 h2 h3 h4 h5 _ _ hE hg hM'
  obtain ⟨hEg, hEn⟩ := hE
  have hEg' : R + (97 + bD n [] (exBalIn M sevm 0x3c0)) - 44 =
      b'.gasLeft + bD b [] (exBalIn M sevm 0x3c0) := hEg
  have hdN : Devm.EqModGas b' (exBal1Next sevm n M bN) := hEn.trans hnx
  have hgR : g = R := by omega
  subst hgR
  refine k b' M' img' h1 h2 h3 h4 h5 hdN ?_
  rw [hM', hdN.returnData]; rfl

/-- The second `balanceOf(self)` call's canonical successor. -/
def exBal2Next (sevm : Sevm) (n : Devm) (M : Mem) (bN : Devm → List B256 → Mem → Devm) : Devm :=
  bN n [] (exBalIn M sevm 0x700)

/-- The memory after the second `balanceOf(self)` and the credited difference at `0x380`. -/
def exBal2Mem (sevm : Sevm) (n : Devm) (M : Mem) (B1 B2 : B256)
    (bN : Devm → List B256 → Mem → Devm) : Mem :=
  (((exBalIn M sevm 0x700).extends [(0x71c, 0x24), (0x780, 0x20)]).write 0x780
    ((exBal2Next sevm n M bN).returnData.take 0x20)).write 0x380 (B2 - B1).toBytes

/-- **The second `balanceOf(self)` and the credited amount, exactly**: `151` fixed plus the
profile's debit. -/
theorem rx_ex_bal2_exact {sevm : Sevm} {b n : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {C B1 B2 : B256}
    {bD : Devm → List B256 → Mem → Nat} {bN : Devm → List B256 → Mem → Devm}
    (hL : ExLive sevm W b σ) (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x6e0)
    (hF : ExFrame img B X B1 C)
    (hbal : StaticWordCallProfile sevm W W C (balanceOfData sevm.currentTarget) B2 U 0x71c 0x24 0x780
      bD bN) (hsub : ¬ B2 < B1)
    (hR0 : 1000 + U ≤ R) (hGb : R + (151 + bD n [] (exBalIn M sevm 0x700)) < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x7a0 → ExFrame img' B X (B2 - B1) C →
      Devm.EqModGas b' (exBal2Next sevm n M bN) → M' = exBal2Mem sevm n M B1 B2 bN →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (R + (151 + bD n [] (exBalIn M sevm 0x700)))) t_2672_c12 Q := by
  obtain ⟨e5, hnx⟩ := hbal.congr [] (exBalIn M sevm 0x700) hn
  refine rx_ex_bal2_core (R := 0) hL hR hW hsz hF (StaticWordCallProfile.okE hbal) hsub (by omega)
    (by omega) ?_
  intro b' M' img' g h1 h2 h3 h4 h5 _ _ hE hg hM'
  obtain ⟨hEg, hEn⟩ := hE
  have hEg' : R + (151 + bD n [] (exBalIn M sevm 0x700)) - 47 =
      b'.gasLeft + bD b [] (exBalIn M sevm 0x700) := hEg
  have hdN : Devm.EqModGas b' (exBal2Next sevm n M bN) := hEn.trans hnx
  have hgR : g = R := by omega
  subst hgR
  refine k b' M' img' h1 h2 h3 h4 h5 hdN ?_
  rw [hM', hdN.returnData]; rfl


/-! ## The front: dispatcher, guards, `_xp_mem` -/

/-- The prologue's memory. -/
abbrev exM0 (sevm : Sevm) : Mem := vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- The words the prefix reads past the memory's end. -/
abbrev exZ (sevm : Sevm) (o : Nat) : B256 :=
  Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD o 32 0)

/-- The canonical base at the fee test: the prefix's storage steps and the `coins[i]` load. -/
def exN2 (sevm : Sevm) (pre : Devm) : Devm :=
  afterSload sevm (exPreBase sevm pre) (coinsBase + exI sevm)

/-- The literal memory at the fee test. -/
def exM2 (sevm : Sevm) (pre : Devm) (x0 x1 x2 : B256) : Mem :=
  Mem.writeWords (exPreMem (exM0 sevm) (pre.getStor sevm.currentTarget))
    (exMidWords x0 x1 x2 (exZ sevm 0x200) (exZ sevm 0x220) (exZ sevm 0x240)
      (balAt (pre.getStor sevm.currentTarget) 0) (balAt (pre.getStor sevm.currentTarget) 1)
      (balAt (pre.getStor sevm.currentTarget) 2) (exDx sevm)
      (((pre.getStor sevm.currentTarget).set lockSlot 1).get (coinsBase + exI sevm)))

/-- **The front's exact charge**: the dispatcher (`422`), the prefix (`661` plus its storage
charges) and `_xp_mem` with its surroundings (`1589` plus the `coins[i]` load). -/
def exHeadCost (sevm : Sevm) (pre : Devm) : Nat :=
  422 + (661 + exPreCost sevm pre) +
    (1589 + sloadCost sevm (exPreBase sevm pre) (coinsBase + exI sevm))

/-- **The dispatcher and the prefix, exactly**: from the frame's entry with
`R + 422 + 661 + exPreCost` to `_xp_mem`'s call idiom with exactly `R`, at the canonical base
`exPreBase` and memory `exPreMem`. -/
theorem rx_ex_head_exact {sevm : Sevm} {pre : Devm} {R : Nat} {Q : Outcome → Prop}
    {W : Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hWb : W pre)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3) (hR0 : 60000 ≤ R)
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
  refine rx_ex_pre_core (b0 := pre) (σ := pre.getStor sevm.currentTarget) (R := 0) hfork
    hstatic ⟨fun _ => rfl, rfl, rfl, hid⟩ hWc hWb hlock hval hkill hi hj
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
    (vyMem_empty_size _) (vyImg_clamps _ _) (by omega) ?_
  intro b1 M1 img1 g1 z0 z1 z2 hB1 hW1 hR1 hWf1 hsz1 _ hg1' hgx1 hb1 hM1 hz0 hz1 hz2
  have hg : g1 = R := by omega
  rw [hg]; rw [hb1] at hB1 hW1 ⊢; rw [hM1] at hR1 hWf1 hsz1 ⊢; rw [hz0, hz1, hz2]
  exact k img1 hB1 hW1 hR1 hWf1 hsz1

/-- **The front, exactly**: from the frame's entry with `R + exHeadCost` to the fee test with
exactly `R`, at the canonical base `exN2` and memory `exM2` themselves. -/
theorem rx_ex_front_exact {sevm : Sevm} {pre : Devm} {R : Nat} {Q : Outcome → Prop}
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
    (hR0 : 60000 ≤ R)
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
  refine rx_ex_head_exact hfork hstatic hlen hcd hsel hid hWc hWb hlock hval hkill hi hj
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


/-! ## The two fee-test branches -/

/-- **Another coin, exactly**: from the fee test to `x` — the test (`10`), the pull, the second
test (`29`) — at a base equal modulo gas to the pull's tail successor. -/
theorem rx_ex_nofee_exact {sevm : Sevm} {b : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C : B256}
    {plD : Devm → List B256 → Mem → Nat} {plN : Devm → List B256 → Mem → Devm}
    (hfee : exI sevm ≠ 2) (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0) (hF : ExFrame img B X D C)
    (hpull : MutableCallProfile sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 0x600 0x64 0x6c0 plD plN)
    (hR0 : 4000 + U ≤ R) (hGb : R + (29 + exPullCost sevm b M 31 plD plN) + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x6e0 → ExFrame img' B X D C →
      Devm.EqModGas b' (exPullTail sevm b M plN) → M' = exPullMem sevm b M plN →
      SFunc.RunEx cert.prog sevm (St b' [] M' R) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [Bytes.toB256 [0x25, 0x17],
        B256.eqCheck (B256.eqCheck (exI sevm) (Bytes.toB256 [2])) 0] M
        (R + (29 + exPullCost sevm b M 31 plD plN) + 10)) (.branchTo t_24d8_c0 11) Q := by
  xr (rx_branchTo_succ (exFeeTest_ne hfee) (g := t_2517_c11) rfl ·)
  rw [show R + (29 + exPullCost sevm b M 31 plD plN) = (R + 29) + exPullCost sevm b M 31 plD plN by
    omega]
  refine rx_ex_pull_exact hfork hdepth hL (Devm.EqModGas.refl _) hW'c hR hW hsz (.inl ⟨rfl, rfl⟩) hF
    hpull (by omega) (by omega) ?_
  intro b' M' img' h1 h2 h3 h4 h5 hn' hM'
  exact rx_ex_test2_ne hfee (k b' M' img' h1 h2 h3 h4 h5 hn' hM')

/-- The fee path's charge from the fee test to `x`. -/
def exFeeMidCost (sevm : Sevm) (n : Devm) (M : Mem) (B1 : B256)
    (bD1 : Devm → List B256 → Mem → Nat) (bN1 : Devm → List B256 → Mem → Devm)
    (plD : Devm → List B256 → Mem → Nat) (plN : Devm → List B256 → Mem → Devm)
    (bD2 : Devm → List B256 → Mem → Nat) : Nat :=
  10 + (97 + bD1 n [] (exBalIn M sevm 0x3c0)) +
    exPullCost sevm (exBal1Next sevm n M bN1) (exBal1Mem sevm n M B1 bN1) 15 plD plN + 29 +
    (151 + bD2 (exPullTail sevm (exBal1Next sevm n M bN1) (exBal1Mem sevm n M B1 bN1) plN) []
      (exBalIn (exPullMem sevm (exBal1Next sevm n M bN1) (exBal1Mem sevm n M B1 bN1) plN) sevm 0x700))

/-- **The fee coin, exactly**: from the fee test to `x` — the test, the first `balanceOf(self)`,
the pull, the second test and the second `balanceOf(self)` — at a base equal modulo gas to the
second read's successor. -/
theorem rx_ex_fee_exact {sevm : Sevm} {b : Devm} {σ : Stor} {R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C B1 B2 : B256}
    {bD1 bD2 plD : Devm → List B256 → Mem → Nat} {bN1 bN2 plN : Devm → List B256 → Mem → Devm}
    (hfee : exI sevm = 2) (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x3c0) (hF : ExFrame img B X D C)
    (hb1 : StaticWordCallProfile sevm W W C (balanceOfData sevm.currentTarget) B1 U 0x3dc 0x24 0x440
      bD1 bN1)
    (hb2 : StaticWordCallProfile sevm W' W' C (balanceOfData sevm.currentTarget) B2 U 0x71c 0x24 0x780
      bD2 bN2) (hsub : ¬ B2 < B1)
    (hpull : MutableCallProfile sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 0x600 0x64 0x6c0 plD plN)
    (hR0 : 4000 + U ≤ R)
    (hGb : R + exFeeMidCost sevm b M B1 bD1 bN1 plD plN bD2 + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x7a0 → ExFrame img' B X (B2 - B1) C →
      Devm.EqModGas b' (exBal2Next sevm (exPullTail sevm (exBal1Next sevm b M bN1)
        (exBal1Mem sevm b M B1 bN1) plN)
        (exPullMem sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) bN2) →
      M' = exBal2Mem sevm (exPullTail sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN)
        (exPullMem sevm (exBal1Next sevm b M bN1) (exBal1Mem sevm b M B1 bN1) plN) B1 B2 bN2 →
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
  refine rx_ex_bal1_exact hL (Devm.EqModGas.refl _) hR hW hsz hF hb1 (by omega) (by omega) ?_
  intro b4 M4 img4 hL4 hR4 hW4 hsz4 hF4 hn4 hM4
  rw [hM4] at hR4 hW4 hsz4 ⊢
  refine rx_ex_pull_exact hfork hdepth hL4 hn4 hW'c hR4 hW4 hsz4 (.inr ⟨rfl, rfl⟩) hF4 hpull
    (by omega) (by omega) ?_
  intro b5 M5 img5 hL5 hR5 hW5 hsz5 hF5 hn5 hM5
  rw [hM5] at hR5 hW5 hsz5 ⊢
  refine rx_ex_test2_eq hfee ?_
  exact rx_ex_bal2_exact hL5 hn5 hR5 hW5 hsz5 hF5 hb2 hsub (by omega) (by omega) k


/-! ## The whole frame -/

/-- The four exact calls' functions, as data fixed before any gas: debit and canonical
successor of the fee coin's two `balanceOf(self)` reads, the pull and the push. -/
structure ExchangeExactCalls where
  balD1 : Devm → List B256 → Mem → Nat
  balN1 : Devm → List B256 → Mem → Devm
  pullD : Devm → List B256 → Mem → Nat
  pullN : Devm → List B256 → Mem → Devm
  balD2 : Devm → List B256 → Mem → Nat
  balN2 : Devm → List B256 → Mem → Devm
  pushD : Devm → List B256 → Mem → Nat
  pushN : Devm → List B256 → Mem → Devm

/-- The fee path's charge after the second `balanceOf(self)`. -/
def exFeeBackCost (sevm : Sevm) (pre : Devm) (P : ExchangeExactCalls) (x0 x1 x2 B1 B2 : B256)
    (amp v : Nat) : Nat :=
  exBackCost sevm
    (exBal2Next sevm (exPullTail sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
      (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN)
      (exPullMem sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
        (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN) P.balN2)
    (exBal2Mem sevm (exPullTail sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
      (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN)
      (exPullMem sevm (exBal1Next sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.balN1)
        (exBal1Mem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balN1) P.pullN) B1 B2 P.balN2)
    6 ((pre.getStor sevm.currentTarget).set lockSlot 1)
    (exW3 (balAt (pre.getStor sevm.currentTarget) 0) (balAt (pre.getStor sevm.currentTarget) 1)
      (balAt (pre.getStor sevm.currentTarget) 2)) (exW3 x0 x1 x2) (B2 - B1) amp v P.pushD P.pushN

/-- Another coin's path's charge after the pull. -/
def exNoFeeBackCost (sevm : Sevm) (pre : Devm) (P : ExchangeExactCalls) (x0 x1 x2 : B256)
    (amp v : Nat) : Nat :=
  exBackCost sevm (exPullTail sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.pullN)
    (exPullMem sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) P.pullN) 26
    ((pre.getStor sevm.currentTarget).set lockSlot 1)
    (exW3 (balAt (pre.getStor sevm.currentTarget) 0) (balAt (pre.getStor sevm.currentTarget) 1)
      (balAt (pre.getStor sevm.currentTarget) 2)) (exW3 x0 x1 x2) (exDx sevm) amp v P.pushD P.pushN

/-- **`exchange`'s exact charge**, a function of the entry, the calls' data and the checked
model words only (no residual gas, no observed run): the front, then the fee coin's or another
coin's path, then the stages after the pull. -/
def exExactCost (sevm : Sevm) (pre : Devm) (P : ExchangeExactCalls) (x0 x1 x2 B1 B2 : B256)
    (amp v : Nat) : Nat :=
  exHeadCost sevm pre + if exI sevm = 2 then
    exFeeMidCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balD1 P.balN1 P.pullD P.pullN
      P.balD2 + exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v
  else
    (29 + exPullCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) 31 P.pullD P.pullN + 10) +
      exNoFeeBackCost sevm pre P x0 x1 x2 amp v

/-- **The `exchange` frame, exactly**: with the calls' data `P` fixed first and every call an
exact profile, for every residual `R ≥ 60000 + U` (headroom only) the frame runs from
`R + exExactCost` to `STOP` with exactly `R` left. -/
theorem rx_ex_frame_exact {sevm : Sevm} {pre : Devm} {s0 : State} {R U amp v : Nat}
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
      StaticWordCallProfile sevm W W ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm))
        (balanceOfData sevm.currentTarget) B1 U 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
      StaticWordCallProfile sevm W' W' ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm))
        (balanceOfData sevm.currentTarget) B2 U 0x71c 0x24 0x780 P.balD2 P.balN2 ∧ ¬ B2 < B1)
    (hpull : MutableCallProfile sevm W W' ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm))
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
        (exDx sevm).toBytes) RawCallOk U 0x600 0x64 0x6c0 P.pullD P.pullN)
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
    (hpush : MutableCallProfile sevm W' W''
      ((pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat)
        (Nat.toB256 v) ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)).toBytes)
      RawCallOk U 0xb60 0x44 0xc00 P.pushD P.pushN)
    (hR0 : 60000 + U ≤ R)
    (hGb : R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W'' D' (exFinal ((pre.getStor sevm.currentTarget).set lockSlot 1)
      sevm (exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi⟩ + exCred sevm B1 B2)
      (exBal (pre.getStor sevm.currentTarget) ⟨(exJ sevm).toNat, hj⟩ -
        exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) -
        exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat))) →
      D'.gasLeft = R → Q (.halted D')) :
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
    obtain ⟨hb1, hb2, hsub⟩ := hbal hfee
    have hD : exCred sevm B1 B2 = B2 - B1 := ite_eq_left hfee
    rw [hD] at hmx hax hres hbi k
    have hc : exExactCost sevm pre P x0 x1 x2 B1 B2 amp v = exHeadCost sevm pre +
        (exFeeMidCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balD1 P.balN1 P.pullD
          P.pullN P.balD2 + exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v) := by
      unfold exExactCost; rw [ite_eq_left hfee]
    rw [hc] at hGb ⊢
    rw [show R + (exHeadCost sevm pre + (exFeeMidCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2)
        B1 P.balD1 P.balN1 P.pullD P.pullN P.balD2 + exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v)) =
        (R + exFeeBackCost sevm pre P x0 x1 x2 B1 B2 amp v +
          exFeeMidCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) B1 P.balD1 P.balN1 P.pullD
            P.pullN P.balD2) + exHeadCost sevm pre by omega]
    refine rx_ex_front_exact hfork hstatic hlen hcd hsel hid hWc hWb hlock hval hkill hi hj hX
      (by omega) ?_
    intro img2 hB2 hW2 hR2 hWf2 hsz2 hF2
    rw [eci] at hF2
    refine rx_ex_fee_exact hfee hfork hdepth ⟨hB2.stor, hB2.id, hWc, hW2⟩ hW'c hR2 hWf2 hsz2 hF2 hb1
      hb2 hsub hpull (by omega) (by omega) ?_
    intro b7 M7 img7 hL7 hR7 hWf7 hsz7 hF7 hn7 hM7
    rw [hM7] at hR7 hWf7 hsz7 ⊢
    exact rx_ex_back_exact hfork hstatic hdepth hL7 hn7 ha1 hi hj hR7 hWf7 hsz7 (.inr ⟨rfl, rfl⟩) hF7
      hmx hax hA hres hy1 hy2 (by rw [ef]; exact hmf) (by rw [ef]; exact hsf) (by rw [ef]; exact hmo)
      (by rw [ef]; exact hmin) (by rw [ef, eaf]; exact hma) (by rw [ef, eaf]; exact hmap) hbi
      (by rw [ef]; exact hbj1) (by rw [ef, eaf]; exact hbj2) hW''c (by rw [ef, ecj]; exact hpush)
      hR0 (by unfold exFeeBackCost at hGb; omega) (by rw [ef, eaf]; exact k)
  · -- another coin
    have hD : exCred sevm B1 B2 = exDx sevm := ite_eq_right hfee
    rw [hD] at hmx hax hres hbi k
    have hc : exExactCost sevm pre P x0 x1 x2 B1 B2 amp v = exHeadCost sevm pre +
        ((29 + exPullCost sevm (exN2 sevm pre) (exM2 sevm pre x0 x1 x2) 31 P.pullD P.pullN + 10) +
          exNoFeeBackCost sevm pre P x0 x1 x2 amp v) := by
      unfold exExactCost; rw [ite_eq_right hfee]
    rw [hc] at hGb ⊢
    rw [show R + (exHeadCost sevm pre + ((29 + exPullCost sevm (exN2 sevm pre)
        (exM2 sevm pre x0 x1 x2) 31 P.pullD P.pullN + 10) + exNoFeeBackCost sevm pre P x0 x1 x2 amp v)) =
        (R + exNoFeeBackCost sevm pre P x0 x1 x2 amp v + (29 + exPullCost sevm (exN2 sevm pre)
          (exM2 sevm pre x0 x1 x2) 31 P.pullD P.pullN) + 10) + exHeadCost sevm pre by omega]
    refine rx_ex_front_exact hfork hstatic hlen hcd hsel hid hWc hWb hlock hval hkill hi hj hX
      (by omega) ?_
    intro img2 hB2 hW2 hR2 hWf2 hsz2 hF2
    rw [eci] at hF2
    refine rx_ex_nofee_exact hfee hfork hdepth ⟨hB2.stor, hB2.id, hWc, hW2⟩ hW'c hR2 hWf2 hsz2 hF2
      hpull (by omega) (by omega) ?_
    intro b5 M5 img5 hL5 hR5 hWf5 hsz5 hF5 hn5 hM5
    rw [hM5] at hR5 hWf5 hsz5 ⊢
    exact rx_ex_back_exact hfork hstatic hdepth hL5 hn5 ha1 hi hj hR5 hWf5 hsz5 (.inl ⟨rfl, rfl⟩) hF5
      hmx hax hA hres hy1 hy2 (by rw [ef]; exact hmf) (by rw [ef]; exact hsf) (by rw [ef]; exact hmo)
      (by rw [ef]; exact hmin) (by rw [ef, eaf]; exact hma) (by rw [ef, eaf]; exact hmap) hbi
      (by rw [ef]; exact hbj1) (by rw [ef, eaf]; exact hbj2) hW''c (by rw [ef, ecj]; exact hpush)
      hR0 (by unfold exNoFeeBackCost at hGb; omega) (by rw [ef, eaf]; exact k)

end Blanc.Lift.Curve3Pool
