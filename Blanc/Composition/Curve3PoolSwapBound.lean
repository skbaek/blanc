import Blanc.Composition.Curve3PoolSwapChain

/-!
# `exchange`'s exact cost fits a word, whatever the frame's entry

`ex_cost_lt`: below `2 ^ 200`, from bounds on the calls' debits. The Newton loops' `fuelCost` are at most their fuel.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (swapCalls swapPullD swapPullN swapPushD swapPushN)
open Blanc.StableSwapNewton

/-- A loop's charge is at most its fuel times the charge of a pass. -/
theorem fuelCost_le {body : Nat → Option Nat} {close : Nat → Nat → Bool} {c1 c2 c3 : Nat → Nat → Nat} {K : Nat}
    (h1 : ∀ a b, c1 a b ≤ K) (h2 : ∀ a b, c2 a b ≤ K) (h3 : ∀ a b, c3 a b ≤ K) :
    ∀ fuel D, fuelCost body close c1 c2 c3 fuel D ≤ fuel * K := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ n ih =>
    intro D
    match n, ih with
    | 0, _ => exact Nat.le_of_eq (by simp only [fuelCost, Nat.zero_mul])
    | 1, _ =>
      unfold fuelCost
      split
      · exact Nat.zero_le _
      · split
        · have := h2 D ‹_›; omega
        · have := h3 D ‹_›; omega
    | m + 2, ih =>
      unfold fuelCost
      split
      · exact Nat.zero_le _
      · split
        · have := h2 D ‹_›
          rw [Nat.add_mul]
          have : 0 ≤ m * K := Nat.zero_le _
          omega
        · have h := ih (m + 1) (by omega) ‹_›
          have h' := h1 D ‹_›
          rw [Nat.add_mul] at *
          omega

theorem costGetD_le (x0 x1 x2 amp : Nat) : costGetD x0 x1 x2 amp ≤ 505 + (59 + 157 + 255 * 2000) := by
  have key : ∀ (b : Nat → Option Nat) (D : Nat), fuelCost b (fun new prev => decide (closeEnough 1 new prev)) gdStepC gdStopC gdCapC 255 D ≤ 255 * 2000 :=
    fun _ D => fuelCost_le (fun a b => by unfold gdStepC; split <;> omega) (fun a b => by unfold gdStopC; split <;> omega)
      (fun a b => by unfold gdCapC; split <;> omega) 255 D
  unfold costGetD
  split
  · split
    · omega
    · split
      · refine Nat.add_le_add_left (Nat.le_trans (Nat.add_le_add_left (key _ _) _) ?_) _
        omega
      · omega
  · omega

theorem ydPostCost_le (c s D ann : Nat) : ydPostCost c s D ann ≤ 363 + 255 * 600 := by
  unfold ydPostCost
  have := fuelCost_le (body := bodyYChk (c * D / (ann * 3)) (s + D / ann) D) (close := fun new prev => decide (closeEnough 1 new prev))
    (c1 := ydStepC) (c2 := ydStopC) (c3 := ydCapC) (K := 600)
    (fun a b => by unfold ydStepC; split <;> omega) (fun a b => by unfold ydStopC; split <;> omega)
    (fun a b => by unfold ydCapC; split <;> omega) 255 D
  omega

theorem gyCoin_le (i j k : Nat) : gyCoinCost i j k ≤ 450 := by
  unfold gyCoinCost
  split
  · omega
  · split <;> omega

theorem gy2_le (i j x x2 D ann : Nat) (cs : Nat × Nat) : gyCostFrom2 i j x x2 D ann cs ≤ 450 + (363 + 255 * 600) := by
  unfold gyCostFrom2
  have h := gyCoin_le i j 2
  split
  · have := ydPostCost_le ‹Nat × Nat›.1 ‹Nat × Nat›.2 D ann
    omega
  · omega

theorem gy1_le (i j x x1 x2 D ann : Nat) (cs : Nat × Nat) : gyCostFrom1 i j x x1 x2 D ann cs ≤ 450 + (450 + (363 + 255 * 600)) := by
  unfold gyCostFrom1
  have h := gyCoin_le i j 1
  split
  · have := gy2_le i j x x2 D ann ‹Nat × Nat›
    omega
  · omega

theorem gy0_le (i j x x0 x1 x2 D ann : Nat) (cs : Nat × Nat) : gyCostFrom0 i j x x0 x1 x2 D ann cs ≤ 450 + (450 + (450 + (363 + 255 * 600))) := by
  unfold gyCostFrom0
  have h := gyCoin_le i j 0
  split
  · have := gy1_le i j x x1 x2 D ann ‹Nat × Nat›
    omega
  · omega

variable {e : Sevm} {d : Devm}

theorem aGas_le (s : Sevm) (b : Devm) : aGas s b ≤ 458 + 4 * 2100 := by
  unfold aGas
  have h1 := sloadCost_le_lit s b futureATimeSlot
  have h2 := sloadCost_le_lit s (afterSload s b futureATimeSlot) futureASlot
  have h3 := sloadCost_le_lit s (afterSload s (afterSload s b futureATimeSlot) futureASlot) initialASlot
  have h4 := sloadCost_le_lit s (afterSload s (afterSload s (afterSload s b futureATimeSlot) futureASlot) initialASlot) initialATimeSlot
  split
  · split <;> omega
  · omega

theorem costGetY_le (s : Sevm) (b : Devm) (amp i j x x0 x1 x2 : Nat) : costGetY s b amp i j x x0 x1 x2 ≤ 2100 + (458 + 4 * 2100) + (505 + (59 + 157 + 255 * 2000) + (450 + (450 + (450 + (363 + 255 * 600))))) := by
  unfold costGetY
  have h := aGas_le s b
  have h1 := costGetD_le x0 x1 x2 amp
  split
  next D ann _ _ =>
    exact Nat.add_le_add (Nat.add_le_add_left h _) (Nat.add_le_add h1 (gy0_le i j x x0 x1 x2 D ann (D, 0)))
  next => omega

theorem rawTail_min (n : Nat) : rawTailCost (min n 32) ≤ 1000 := rawTail_le _ (by omega)

/-- **The cost fits**, from bounds on the calls' debits. -/
theorem exBack_le {s : Sevm} {n : Devm} {M : Mem} {c0 : Nat} {σ : Stor} {B X : Nat → B256} {D : B256} {amp v KP : Nat}
    {pD : Devm → List B256 → Mem → Nat} {pN : Devm → List B256 → Mem → Devm} (hc0 : c0 ≤ 26) (hpd : ∀ b S M, pD b S M ≤ KP) :
    exBackCost s n M c0 σ B X D amp v pD pN ≤ 20000 + 700000 + 60000 + KP := by
  have hcost : exBackCost s n M c0 σ B X D amp v pD pN =
      279 + c0 + 3540 + (3906 + costGetY s n amp (exI s).toNat (exJ s).toNat
        (exXw s X D).toNat (X 0).toNat (X 1).toNat (X 2).toNat) +
      (612 + sloadCost s (aBase s n) (Bytes.toB256 [0x02])) +
      exTailCost s (afterSload s (aBase s n) (Bytes.toB256 [0x02]))
        (exBackDyMem s M σ X D v) σ B D
        (exDyFee (X (exJ s).toNat) (Nat.toB256 v) (σ.get feeSlot))
        (exDyOut (X (exJ s).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ s).toNat))
        pD pN := rfl
  rw [hcost]
  have h1 := costGetY_le s n amp (exI s).toNat (exJ s).toNat (exXw s X D).toNat (X 0).toNat (X 1).toNat (X 2).toNat
  have h2 := sloadCost_le_lit s (aBase s n) (Bytes.toB256 [0x02])
  unfold exTailCost exPushCost exStoreCost
  have h3 := sloadCost_le_lit s (afterSload s (aBase s n) (Bytes.toB256 [0x02])) (Bytes.toB256 [3])
  generalize exTailN2 s _ _ _ _ _ _ _ = T2
  generalize exStoreI2 _ _ _ _ _ = Mf
  have h6 := sloadCost_le_lit s T2 (coinsBase + Sevm.dataWord s (Bytes.toB256 [36]))
  have h7 := hpd (exPushIn s T2) [] (Mf.write 0xc0 (Bytes.toB256 [0]).toBytes)
  have h8 := rawTail_min (exPushNext s T2 Mf pN).returnData.length
  have h9 := sstoreCost_le_lit s (rawTailBaseNext s (exPushNext s T2 Mf pN) [] (exPushNext s T2 Mf pN).memory exPushSite)
    (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])
  have h4 : ∀ a k v', sstoreCost s a k v' ≤ 22100 := fun a k v' => sstoreCost_le_lit s a k v'
  have h4a := h4 (afterSload s (afterSload s (aBase s n) (Bytes.toB256 [0x02])) (Bytes.toB256 [3]))
    (balancesBase + Sevm.dataWord s (Bytes.toB256 [4])) (exVi s B D)
  have h4b := h4 (afterSstore s (afterSload s (afterSload s (aBase s n) (Bytes.toB256 [0x02])) (Bytes.toB256 [3]))
    (balancesBase + Sevm.dataWord s (Bytes.toB256 [4])) (exVi s B D)) (balancesBase + Sevm.dataWord s (Bytes.toB256 [36]))
    (exVj s σ B (exDyFee (X (exJ s).toNat) (Nat.toB256 v) (σ.get feeSlot)) (exDyOut (X (exJ s).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ s).toNat)))
  omega

theorem exPull_le {s : Sevm} {n : Devm} {M : Mem} {c0 K : Nat} {plD : Devm → List B256 → Mem → Nat} {plN : Devm → List B256 → Mem → Devm}
    (hc0 : c0 ≤ 31) (h : ∀ b S M, plD b S M ≤ K) : exPullCost s n M c0 plD plN ≤ 2000 + K := by
  unfold exPullCost
  have h1 := h (exPullN2 s n M) [] (exPullI2 M s)
  have h2 := rawTail_min (exPullNext s n M plN).returnData.length
  omega

theorem exHead_le (s : Sevm) (p : Devm) : exHeadCost s p ≤ 200000 := by
  unfold exHeadCost exPreCost
  have h1 := sloadCost_le_lit s p (Bytes.toB256 [255, 255, 255])
  have h2 := sstoreCost_le_lit s (afterSload s p (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])
  have h3 := sloadCost_le_lit s (afterSstore s (afterSload s p (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])
  have h4 := sloadCost_le_lit s (exPreLockBase s p) balancesBase
  have h5 := sloadCost_le_lit s (afterSload s (exPreLockBase s p) balancesBase) (balancesBase + Bytes.toB256 [1])
  have h6 := sloadCost_le_lit s (afterSload s (afterSload s (exPreLockBase s p) balancesBase) (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2])
  have h7 := sloadCost_le_lit s (exPreBase s p) (coinsBase + exI s)
  omega

/-- **`exchange`'s exact cost fits a word.** -/
theorem ex_cost_lt {s : Sevm} {p : Devm} {P : ExchangeExactCalls} {x0 x1 x2 B1 B2 : B256} {amp v : Nat} {K : Nat}
    (hK : K ≤ 2 ^ 100)
    (h1 : ∀ b S M, P.balD1 b S M ≤ K) (h2 : ∀ b S M, P.balD2 b S M ≤ K) (h3 : ∀ b S M, P.pullD b S M ≤ K) (h4 : ∀ b S M, P.pushD b S M ≤ K) :
    exExactCost s p P x0 x1 x2 B1 B2 amp v < 2 ^ 200 := by
  unfold exExactCost
  have hH := exHead_le s p
  split
  · unfold exFeeMidCost exFeeBackCost
    have b1 := h1 (exN2 s p) [] (exBalIn (exM2 s p x0 x1 x2) s 0x3c0)
    have b2 := h2 (exPullTail s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) P.balN1) (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 P.balN1) P.pullN) []
      (exBalIn (exPullMem s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) P.balN1) (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 P.balN1) P.pullN) s 0x700)
    have b3 := exPull_le (s := s) (n := exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) P.balN1) (M := exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 P.balN1) (c0 := 15) (plN := P.pullN) (by decide) h3
    have b4 := exBack_le (s := s) (n := exBal2Next s (exPullTail s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) P.balN1)
      (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 P.balN1) P.pullN)
      (exPullMem s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) P.balN1)
        (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 P.balN1) P.pullN) P.balN2)
      (M := exBal2Mem s (exPullTail s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) P.balN1)
      (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 P.balN1) P.pullN)
      (exPullMem s (exBal1Next s (exN2 s p) (exM2 s p x0 x1 x2) P.balN1)
        (exBal1Mem s (exN2 s p) (exM2 s p x0 x1 x2) B1 P.balN1) P.pullN) B1 B2 P.balN2) (c0 := 6)
      (σ := (p.getStor s.currentTarget).set lockSlot 1) (B := exW3 (balAt (p.getStor s.currentTarget) 0) (balAt (p.getStor s.currentTarget) 1)
      (balAt (p.getStor s.currentTarget) 2)) (X := exW3 x0 x1 x2) (D := B2 - B1) (amp := amp) (v := v) (pN := P.pushN) (by decide) h4
    omega
  · unfold exNoFeeBackCost
    have b3 := exPull_le (s := s) (n := exN2 s p) (M := exM2 s p x0 x1 x2) (c0 := 31) (plN := P.pullN) (by decide) h3
    have b4 := exBack_le (s := s) (n := exPullTail s (exN2 s p) (exM2 s p x0 x1 x2) P.pullN)
      (M := exPullMem s (exN2 s p) (exM2 s p x0 x1 x2) P.pullN) (c0 := 26)
      (σ := (p.getStor s.currentTarget).set lockSlot 1) (B := exW3 (balAt (p.getStor s.currentTarget) 0) (balAt (p.getStor s.currentTarget) 1)
      (balAt (p.getStor s.currentTarget) 2)) (X := exW3 x0 x1 x2) (D := exDx s) (amp := amp) (v := v) (pN := P.pushN) (by decide) h4
    omega

end Blanc.Composition.Curve3PoolPublic
