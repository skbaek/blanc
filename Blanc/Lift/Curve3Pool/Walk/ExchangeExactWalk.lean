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

end Blanc.Lift.Curve3Pool
