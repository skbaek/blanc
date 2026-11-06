import Blanc.Composition.Curve3PoolSwapPay

/-!
# `exchange`'s canonical chain from a cold start: the prefix, and everything after the pull

`swap_head`: the lock, the kill flag, the books and `coins[i]`, up to the fee test. `swap_back`: `_A`, `get_y`, the stores,
the push, the event and the lock's release, from the base the pull leaves.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (swapPullD swapPullN swapPushD swapPushN)

/-- The pool's storage while the lock is held. -/
noncomputable abbrev lockedStor (w : Jaune.State) : Stor := (w.getStor pool).set lockW (Bytes.toB256 [1])

/-- The pool's warm keys at the fee test. -/
def headK (i : Nat) : List B256 :=
  (coinsBase + Nat.toB256 i) :: (balancesBase + Bytes.toB256 [2]) :: (balancesBase + Bytes.toB256 [1]) :: balancesBase ::
    Bytes.toB256 [15] :: lockW :: lockW :: []

theorem head_coin_fresh : ∀ i : Fin 3, coinsBase + Nat.toB256 i.val ∉ (balancesBase + Bytes.toB256 [2]) :: (balancesBase + Bytes.toB256 [1]) :: balancesBase ::
    Bytes.toB256 [15] :: lockW :: lockW :: [] := by decide

theorem bal_in_head : ∀ i k : Fin 3, balancesBase + Nat.toB256 k.val ∈ headK i.val := by decide

theorem coin_not_head : ∀ i j : Fin 3, i ≠ j → coinsBase + Nat.toB256 j.val ∉ headK i.val := by decide

theorem bal_ne_lockW : ∀ k : Fin 3, balancesBase + Nat.toB256 k.val ≠ lockW := by decide

theorem bal_ne_bal' : ∀ i j : Fin 3, i ≠ j → balancesBase + Nat.toB256 i.val ≠ balancesBase + Nat.toB256 j.val := by decide

theorem a_not_head : (∀ i : Fin 3, futureATimeSlot ∉ headK i.val) ∧ (∀ i : Fin 3, futureASlot ∉ headK i.val) ∧
    (∀ i : Fin 3, initialASlot ∉ headK i.val) ∧ (∀ i : Fin 3, initialATimeSlot ∉ headK i.val) := by decide

theorem fee_not_head : (∀ i : Fin 3, Bytes.toB256 [0x02] ∉ headK i.val) ∧ (∀ i : Fin 3, Bytes.toB256 [3] ∉ headK i.val) := by decide

theorem coin_ne_a : (∀ j : Fin 3, coinsBase + Nat.toB256 j.val ≠ initialATimeSlot) ∧ (∀ j : Fin 3, coinsBase + Nat.toB256 j.val ≠ initialASlot) ∧
    (∀ j : Fin 3, coinsBase + Nat.toB256 j.val ≠ futureASlot) ∧ (∀ j : Fin 3, coinsBase + Nat.toB256 j.val ≠ futureATimeSlot) := by decide

theorem coin_ne_3 : ∀ j : Fin 3, coinsBase + Nat.toB256 j.val ≠ Bytes.toB256 [3] := by decide

theorem coin_ne_2 : ∀ j : Fin 3, coinsBase + Nat.toB256 j.val ≠ Bytes.toB256 [0x02] := by decide

theorem coin_ne_pool : ∀ j : Fin 3, coinAt j ≠ pool := by decide

theorem coin_ne_bal' : ∀ j k : Fin 3, coinsBase + Nat.toB256 j.val ≠ balancesBase + Nat.toB256 k.val := by decide

theorem coin_ne_bal (j k : Fin 3) {kC kB : B256} (h1 : kC = coinsBase + Nat.toB256 j.val) (h2 : kB = balancesBase + Nat.toB256 k.val) : kC ≠ kB := by
  rw [h1, h2]; exact coin_ne_bal' j k

theorem coinHeld_lt {w : Jaune.State} {a : Adr} {k : Fin 3} : coinHeld w a k < 2 ^ 256 := by
  unfold coinHeld
  split
  · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (B256.toNat_lt _)
  · exact B256.toNat_lt _

section Head

variable {s : Sevm} {p : Devm} {w : Jaune.State} {E : Adr}

/-- **The prefix**: the lock read and set, the kill flag, three books and `coins[i]`. -/
theorem swap_head (f : CoinStand s p w E) (hlock : (w.getStor pool).get lockW = 0) {i : Fin 3} (hi : exI s = Nat.toB256 i.val) :
    exHeadCost s p = 35272 ∧ Mv [pool] 0 p (exN2 s p) ∧ At s.currentTarget (headK i.val) (lockedStor w) (exN2 s p) := by
  have hg : s.benvStat.rules.gas.storageClearRefund = 4800 := CoveredFork.rules_storageClearRefund f.fork
  have hx : s.currentTarget = pool ∨ s.currentTarget = c3 ∨ s.currentTarget = dai ∨ s.currentTarget = usdc ∨ s.currentTarget = usdt := Or.inl f.target
  have hS : p.getStor s.currentTarget = w.getStor pool := by rw [f.target]; exact (f.stor pool (Or.inl rfl)).1
  have hO : (getOrigAcct s s.currentTarget).stor = w.getStor pool := by rw [f.target]; exact (f.stor pool (Or.inl rfl)).2
  have hA : At s.currentTarget [] (w.getStor pool) p :=
    ⟨fun k => ⟨fun h => absurd h (f.keysCold _), fun h => absurd h List.not_mem_nil⟩, hS⟩
  have a1 := hA.sload lockW
  have m1 := mv_afterSload s p lockW
  have c1 := m1.clean f.clean
  have hv : (afterSload s p lockW).getOrigStorVal s s.currentTarget lockW = 0 := by
    rw [c1.orig, hO, hlock]
  have m2 : Mv [s.currentTarget] 0 (afterSload s p lockW) (afterSstore s (afterSload s p lockW) lockW (Bytes.toB256 [1])) :=
    mv_afterSstore s _ _ _ (by rw [hv, a1.val, hlock, first_refund, ite_eq_right (fun e => e.1 rfl)])
  have a2 := a1.sstore lockW (Bytes.toB256 [1])
  have a3 := a2.sload (Bytes.toB256 [15])
  have m3 := mv_afterSload s (afterSstore s (afterSload s p lockW) lockW (Bytes.toB256 [1])) (Bytes.toB256 [15])
  obtain ⟨L, hL⟩ : ∃ L, L = exPreLockBase s p := ⟨_, rfl⟩
  have hLe : L = afterSload s (afterSstore s (afterSload s p lockW) lockW (Bytes.toB256 [1])) (Bytes.toB256 [15]) := hL
  rw [← hLe] at a3 m3
  have a4 := a3.sload balancesBase
  have a5 := a4.sload (balancesBase + Bytes.toB256 [1])
  have a6 := a5.sload (balancesBase + Bytes.toB256 [2])
  have m6 := ((mv_afterSload s L balancesBase).trans (mv_afterSload s _ (balancesBase + Bytes.toB256 [1]))).trans
    (mv_afterSload s _ (balancesBase + Bytes.toB256 [2]))
  have hbase : exPreBase s p = afterSload s (afterSload s (afterSload s L balancesBase) (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2]) := by
    rw [hL]; rfl
  rw [← hbase] at a6 m6
  have hn : exN2 s p = afterSload s (exPreBase s p) (coinsBase + Nat.toB256 i.val) := by
    unfold exN2; rw [hi]
  refine ⟨?_, ?_, ?_⟩
  · have hP : exPreCost s p = sloadCost s p lockW + sstoreCost s (afterSload s p lockW) lockW (Bytes.toB256 [1]) +
        sloadCost s (afterSstore s (afterSload s p lockW) lockW (Bytes.toB256 [1])) (Bytes.toB256 [15]) + sloadCost s L balancesBase +
        sloadCost s (afterSload s L balancesBase) (balancesBase + Bytes.toB256 [1]) +
        sloadCost s (afterSload s (afterSload s L balancesBase) (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2]) := by
      rw [hL]; rfl
    unfold exHeadCost
    rw [hP, hA.sloadCost_cold List.not_mem_nil, a1.sstoreCost_warm List.mem_cons_self, hv, hlock, first_value,
      a2.sloadCost_cold (by decide), a3.sloadCost_cold (by decide), a4.sloadCost_cold (by decide), a5.sloadCost_cold (by decide), hi,
      a6.sloadCost_cold (head_coin_fresh i)]
    rfl
  · rw [hn]
    have := ((((m1.trans m2).trans m3).trans m6).trans (mv_afterSload s _ (coinsBase + Nat.toB256 i.val)))
    rw [f.target] at this
    exact this.one (fun a ha => by
      simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using ha) (by simp only [Int.add_zero])
  · rw [hn]
    exact a6.sload _

/-! ## `_A` -/

/-- The keys `_A` warms on top of `K`, at timestamp `t`. -/
def aKeys (w : Jaune.State) (t : Nat) (K : List B256) : List B256 :=
  if t < word w pool futureATimeSlot then initialATimeSlot :: initialASlot :: futureASlot :: futureATimeSlot :: K
  else futureASlot :: futureATimeSlot :: K

/-- **`_A`, its slots cold.** -/
theorem a_stage {K : List B256} {n : Devm} (hA : At s.currentTarget K (lockedStor w) n) (ht : (⟨s.currentTarget, futureATimeSlot⟩ : Adr × B256) ∉ n.accessedStorageKeys)
    (h1 : futureATimeSlot ∉ K) (h2 : futureASlot ∉ K) (h3 : initialASlot ∉ K) (h4 : initialATimeSlot ∉ K) :
    aGas s n = 4285 + rampReadGas w s.benvStat.time.toNat ∧ Mv [s.currentTarget] 0 n (aBase s n) ∧
      At s.currentTarget (aKeys w s.benvStat.time.toNat K) (lockedStor w) (aBase s n) := by
  have hget : ∀ k, k ≠ lockW → (lockedStor w).get k = (w.getStor pool).get k := fun k hk => Stor.get_set_ne _ (Ne.symm hk) _
  have v1 : (n.getStorVal s.currentTarget futureATimeSlot).toNat = word w pool futureATimeSlot := by
    rw [hA.val, hget _ (by decide)]; rfl
  have v2 : (n.getStorVal s.currentTarget futureASlot).toNat = word w pool futureASlot := by
    rw [hA.val, hget _ (by decide)]; rfl
  have v3 : (n.getStorVal s.currentTarget initialASlot).toNat = word w pool initialASlot := by
    rw [hA.val, hget _ (by decide)]; rfl
  have a1 := hA.sload futureATimeSlot
  have a2 := a1.sload futureASlot
  have a3 := a2.sload initialASlot
  have a4 := a3.sload initialATimeSlot
  have c1 := hA.sloadCost_cold h1
  have c2 := a1.sloadCost_cold (K := futureATimeSlot :: K) (k := futureASlot) (by
    simp only [List.mem_cons, not_or]; exact ⟨by decide, h2⟩)
  have c3 := a2.sloadCost_cold (k := initialASlot) (by
    simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, h3⟩)
  have c4 := a3.sloadCost_cold (k := initialATimeSlot) (by
    simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, h4⟩)
  unfold aGas aBase aKeys rampReadGas
  rw [v1, v2, v3]
  by_cases hr : s.benvStat.time.toNat < word w pool futureATimeSlot
  · simp only [hr, ↓reduceIte, c1, c2, c3, c4]
    refine ⟨?_, ?_, a4⟩
    · split <;> omega
    · exact (((((mv_afterSload s n _).trans (mv_afterSload s _ _)).trans (mv_afterSload s _ _)).trans (mv_afterSload s _ _))).one (fun a ha => by
        simpa only [List.mem_append, List.mem_singleton, or_self] using ha) rfl
  · simp only [hr, ↓reduceIte, c1, c2]
    refine ⟨trivial, ?_, a2⟩
    exact ((mv_afterSload s n _).trans (mv_afterSload s _ _)).one (fun a ha => by
        simpa only [List.mem_append, List.mem_singleton, or_self] using ha) rfl

theorem sub_sub_word {x a b : B256} (h : a.toNat + b.toNat ≤ x.toNat) (hn : a.toNat + b.toNat < 2 ^ 256) :
    x - a - b = x - (a + b) := by
  apply B256.toNat_inj
  have hab : (a + b).toNat = a.toNat + b.toNat := toNat_add_of hn
  have h1 : (x - a).toNat = x.toNat - a.toNat := B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.2 (by omega))
  rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.2 (by rw [h1]; omega)), h1,
    B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.2 (by rw [hab]; exact h)), hab]
  omega

/-! ## After the pull -/

theorem Mv.st {T : List Adr} {r : Int} {b B : Devm} (h : Mv T r b B) (S : List B256) (M : Mem) (G : Nat) : Mv T r b (St B S M G) :=
  ⟨fun x hx => ⟨(h.same x hx).keys, (h.same x hx).stor, (h.same x hx).warm⟩, h.refund,
    fun hc => ⟨(h.clean hc).created, (h.clean hc).del, (h.clean hc).error⟩⟩

theorem Mv.cast {T T' : List Adr} {r r' : Int} {b b' : Devm} (h : Mv T r b b') (hT : ∀ a ∈ T, a ∈ T') (hr : r = r') : Mv T' r' b b' :=
  hr ▸ h.mono hT

theorem ext_pushSite {b : Devm} {S : List B256} {M : Mem} (h : M.size = 0xbc0) : ext b S M 0xb60 0x44 0xc00 0x20 = 10 := by
  rw [ext_size _ _ _ _ h]; decide

/-- The words after the pull, and what `exchange`'s back half stands on. -/
structure SwapBack (s : Sevm) (p : Devm) (w : Jaune.State) (E : Adr) (i j : Fin 3) (D O A : B256) (dy : Nat) : Prop where
  stand : CoinStand s p w E
  static : s.isStatic = false
  iw : exI s = Nat.toB256 i.val
  jw : exJ s = Nat.toB256 j.val
  differ : i ≠ j
  named : E ≠ 0
  coinJ : ((lockedStor w).get (coinsBase + Nat.toB256 j.val)).toAdr = coinAt j
  lock : (w.getStor pool).get lockW = 0
  /-- The credit fits above the books. -/
  credit : D.toNat + ((lockedStor w).get (balancesBase + Nat.toB256 i.val)).toNat < 2 ^ 256
  /-- The output and the admin's cut stay below the books. -/
  below : O.toNat + A.toNat < ((lockedStor w).get (balancesBase + Nat.toB256 j.val)).toNat
  /-- The output as a word. -/
  out : O = Nat.toB256 dy
  /-- The pool can pay, and `E`'s credit fits. -/
  pays : dy ≤ coinHeld w pool j ∧ CreditFits w E j (netOf w j dy) ∧ (j = 2 → UsdtFeeFits w dy)

/-- What the pool's books become. -/
noncomputable def swapStored (w : Jaune.State) (i j : Fin 3) (D O A : B256) : Stor :=
  (((lockedStor w).set (balancesBase + Nat.toB256 i.val) ((lockedStor w).get (balancesBase + Nat.toB256 i.val) + D)).set
    (balancesBase + Nat.toB256 j.val) ((lockedStor w).get (balancesBase + Nat.toB256 j.val) - (O + A))).set lockW (Bytes.toB256 [0])

/-- **Everything after the pull**, from the base it leaves. `pD` and `pN` are coin `j`'s. -/
theorem swap_back {i j : Fin 3} {D O A F : B256} {dy c0 amp v nw : Nat} {B X : Nat → B256} {n : Devm} {M : Mem}
    {Tn : List Adr} {rn : Int} (g : SwapBack s p w E i j D O A dy)
    (hBi : B (exI s).toNat = (lockedStor w).get (balancesBase + Nat.toB256 i.val))
    (hBj : B (exJ s).toNat = (lockedStor w).get (balancesBase + Nat.toB256 j.val))
    (hF : exDyFee (X (exJ s).toNat) (Nat.toB256 v) ((lockedStor w).get feeSlot) = F)
    (hO : exDyOut (X (exJ s).toNat) (Nat.toB256 v) ((lockedStor w).get feeSlot) (exRate (exJ s).toNat) = O)
    (hA' : exAdm F ((lockedStor w).get adminFeeSlot) (exRate (exJ s).toNat) = A)
    (hA : At s.currentTarget (headK i.val) (lockedStor w) n) (mv : Mv Tn rn p n) (hT : ∀ x ∈ coinT j, x ∉ Tn)
    (hY : ∀ b, costGetY s b amp (exI s).toNat (exJ s).toNat (exXw s X D).toNat (X 0).toNat (X 1).toNat (X 2).toNat = 2100 + aGas s b + nw)
    (win : ExPushWin s (exStoreI2 (exBackDyMem s M (lockedStor w) X D v) s F ((lockedStor w).get adminFeeSlot) O) O) :
    exBackCost s n M c0 (lockedStor w) B X D amp v (swapPushD s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j)
        (swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) =
      279 + c0 + 3540 + (3906 + (2100 + (4285 + rampReadGas w s.benvStat.time.toNat) + nw)) + (612 + 2100) +
        (1225 + (2100 + creditG ((lockedStor w).get (balancesBase + Nat.toB256 i.val)).toNat D.toNat + debitG (O + A).toNat) +
          (2340 + 2100 + (2600 + 10 + payG w E j dy) + rawTailCost (replyLen j) + 100)) ∧
    ∀ D', ExEnd s (exTailN2 s (afterSload s (aBase s n) (Bytes.toB256 [0x02])) (exBackDyMem s M (lockedStor w) X D v) (lockedStor w) B D F O)
        (exStoreI2 (exBackDyMem s M (lockedStor w) X D v) s F ((lockedStor w).get adminFeeSlot) O)
        (swapPushN s ((lockedStor w).get (coinsBase + Nat.toB256 j.val)) j) D' →
      Mv (Tn ++ pool :: coinT j) (rn + ((4800 * empties (rawHeld w pool j) dy : Nat) : Int) + 19900) p D' ∧
        D'.getStor pool = swapStored w i j D O A ∧ D'.getStor (coinAt j) = paidStor w E j dy := by
  have f := g.stand
  have hg : s.benvStat.rules.gas.storageClearRefund = 4800 := CoveredFork.rules_storageClearRefund f.fork
  have ht := f.target
  have hO0 : (getOrigAcct s s.currentTarget).stor = w.getStor pool := by rw [ht]; exact (f.stor pool (Or.inl rfl)).2
  have hIw : Sevm.dataWord s (Bytes.toB256 [4]) = Nat.toB256 i.val := g.iw
  have hJw : Sevm.dataWord s (Bytes.toB256 [36]) = Nat.toB256 j.val := g.jw
  have hget : ∀ k, k ≠ lockW → (lockedStor w).get k = (w.getStor pool).get k := fun k hk => Stor.get_set_ne _ (Ne.symm hk) _
  have hor : ∀ k, k ≠ lockW → (getOrigAcct s s.currentTarget).stor.get k = (lockedStor w).get k := fun k hk => by rw [hO0, hget k hk]
  obtain ⟨kI, hkI⟩ : ∃ k, k = balancesBase + Nat.toB256 i.val := ⟨_, rfl⟩
  obtain ⟨kJ, hkJ⟩ : ∃ k, k = balancesBase + Nat.toB256 j.val := ⟨_, rfl⟩
  have hdI : kI ≠ lockW := by rw [hkI]; exact bal_ne_lockW i
  have hdJ : kJ ≠ lockW := by rw [hkJ]; exact bal_ne_lockW j
  have hdIJ : kI ≠ kJ := by rw [hkI, hkJ]; exact bal_ne_bal' i j g.differ
  rw [← hkI] at hBi
  rw [← hkJ] at hBj
  have hcred := g.credit
  have hbel := g.below
  rw [← hkI] at hcred
  rw [← hkJ] at hbel
  obtain ⟨gA, mA, aA⟩ := a_stage (K := headK i.val) hA (fun m => a_not_head.1 i ((hA.keys _).1 m)) (a_not_head.1 i) (a_not_head.2.1 i) (a_not_head.2.2.1 i) (a_not_head.2.2.2 i)
  obtain ⟨K1, hK1⟩ : ∃ K, K = aKeys w s.benvStat.time.toNat (headK i.val) := ⟨_, rfl⟩
  rw [← hK1] at aA
  have hmemK : ∀ k, k ∈ headK i.val → k ∈ K1 := fun k hk => by
    rw [hK1]; unfold aKeys; split <;> simp only [List.mem_cons, hk, or_true]
  have hnotK : ∀ k, k ∉ headK i.val → k ≠ initialATimeSlot → k ≠ initialASlot → k ≠ futureASlot → k ≠ futureATimeSlot → k ∉ K1 := fun k h h1 h2 h3 h4 => by
    rw [hK1]; unfold aKeys; split <;> simp only [List.mem_cons, not_or] <;> simp only [h1, h2, h3, h4, not_false_eq_true, true_and] <;> exact h
  have n2 : Bytes.toB256 [0x02] ∉ K1 := hnotK _ (fee_not_head.1 i) (by decide) (by decide) (by decide) (by decide)
  have n3 : Bytes.toB256 [3] ∉ K1 := hnotK _ (fee_not_head.2 i) (by decide) (by decide) (by decide) (by decide)
  have nC : coinsBase + Nat.toB256 j.val ∉ K1 := hnotK _ (coin_not_head i j g.differ) (coin_ne_a.1 j) (coin_ne_a.2.1 j) (coin_ne_a.2.2.1 j) (coin_ne_a.2.2.2 j)
  have mI : kI ∈ K1 := hmemK _ (by rw [hkI]; exact bal_in_head i i)
  have mJ : kJ ∈ K1 := hmemK _ (by rw [hkJ]; exact bal_in_head i j)
  have mL : lockW ∈ K1 := hmemK _ (by simp only [headK, List.mem_cons, true_or, or_true])
  obtain ⟨N, hN⟩ : ∃ N, N = afterSload s (aBase s n) (Bytes.toB256 [0x02]) := ⟨_, rfl⟩
  have a2 : At s.currentTarget (Bytes.toB256 [0x02] :: K1) (lockedStor w) N := by rw [hN]; exact aA.sload _
  have m2 : Mv [s.currentTarget] 0 (aBase s n) N := by rw [hN]; exact mv_afterSload ..
  have a3 := a2.sload (Bytes.toB256 [3])
  have m3 := mv_afterSload s N (Bytes.toB256 [3])
  have mUp := ((mv.trans mA).trans m2).trans m3
  have c3 := mUp.clean f.clean
  have mk2 : ∀ {k}, k ∈ K1 → k ∈ Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1 := fun h => by
    simp only [List.mem_cons, h, or_true]
  have f1 : Fresh s (afterSload s N (Bytes.toB256 [3])) kI ((lockedStor w).get kI) := ⟨c3, hor _ hdI, a3.val _⟩
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = afterSstore s (afterSload s N (Bytes.toB256 [3])) kI ((lockedStor w).get kI + D) := ⟨_, rfl⟩
  have m4 : Mv [s.currentTarget] 0 (afterSload s N (Bytes.toB256 [3])) B1 := by rw [hB1]; exact mv_credit f1 (by omega)
  have a4 : At s.currentTarget (kI :: Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1) ((lockedStor w).set kI ((lockedStor w).get kI + D)) B1 := by
    rw [hB1]; exact a3.sstore kI _
  have c4 := m4.clean c3
  have vJ : ((lockedStor w).set kI ((lockedStor w).get kI + D)).get kJ = (lockedStor w).get kJ := Stor.get_set_ne _ hdIJ _
  have f2 : Fresh s B1 kJ ((lockedStor w).get kJ) := ⟨c4, hor _ hdJ, by rw [a4.val, vJ]⟩
  have hsum : (O + A).toNat = O.toNat + A.toNat := toNat_add_of (by have := B256.toNat_lt ((lockedStor w).get kJ); omega)
  have hle : (O + A).toNat ≤ ((lockedStor w).get kJ).toNat := by omega
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = afterSstore s B1 kJ ((lockedStor w).get kJ - (O + A)) := ⟨_, rfl⟩
  have m5 : Mv [s.currentTarget] 0 B1 B2 := by
    have := mv_debit (v := O + A) f2 hle hg
    have hE : empties ((lockedStor w).get kJ).toNat (O + A).toNat = 0 := ite_eq_right (fun e => by omega)
    rw [hE] at this
    rw [hB2]
    exact this
  have a5 : At s.currentTarget (kJ :: kI :: Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1)
      (((lockedStor w).set kI ((lockedStor w).get kI + D)).set kJ ((lockedStor w).get kJ - (O + A))) B2 := by
    rw [hB2]; exact a4.sstore kJ _
  obtain ⟨σ2, hσ2⟩ : ∃ σ2, σ2 = ((lockedStor w).set kI ((lockedStor w).get kI + D)).set kJ ((lockedStor w).get kJ - (O + A)) := ⟨_, rfl⟩
  rw [← hσ2] at a5
  have hVj : exVj s (lockedStor w) B F O = (lockedStor w).get kJ - (O + A) := by
    show B (exJ s).toNat - O - exAdm F ((lockedStor w).get adminFeeSlot) (exRate (exJ s).toNat) = _
    rw [hBj, hA', sub_sub_word (by omega) (by have := B256.toNat_lt ((lockedStor w).get kJ); omega)]
  have hVi : exVi s B D = (lockedStor w).get kI + D := by
    show B (exI s).toNat + D = _
    rw [hBi]
  have hbase : exStoreBase s N (exVi s B D) (exVj s (lockedStor w) B F O) = B2 := by
    unfold exStoreBase
    rw [hVi, hVj, hIw, hJw, ← hkI, ← hkJ, hB2, hB1]
  obtain ⟨Mb, hMb⟩ : ∃ Mb, Mb = exBackDyMem s M (lockedStor w) X D v := ⟨_, rfl⟩
  obtain ⟨Mf, hMf⟩ : ∃ Mf, Mf = exStoreI2 Mb s F ((lockedStor w).get adminFeeSlot) O := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T2, T2 = exTailN2 s N Mb (lockedStor w) B D F O := ⟨_, rfl⟩
  have mId : Mv ([] ++ []) (0 + 0) B2 T2 := by
    rw [hT2]
    unfold exTailN2 exTailN1
    rw [hbase]
    exact (mv_identity ..).trans (mv_identity ..)
  have a5' : At s.currentTarget (kJ :: kI :: Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1) σ2 T2 := a5.ofMv mId (by simp only [List.append_nil, List.not_mem_nil, not_false_eq_true])
  obtain ⟨kC, hkC⟩ : ∃ k, k = coinsBase + Nat.toB256 j.val := ⟨_, rfl⟩
  have hPushIn : exPushIn s T2 = afterSload s T2 kC := by unfold exPushIn; rw [hJw, hkC]
  have m6 := mv_afterSload s T2 kC
  rw [← hPushIn] at m6
  have a6 : At s.currentTarget (kC :: kJ :: kI :: Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1) σ2 (exPushIn s T2) := by rw [hPushIn]; exact a5'.sload kC
  have mTo : Mv (Tn ++ [pool]) rn p (exPushIn s T2) := by
    refine Mv.cast (((((mUp.trans m4).trans m5).trans mId).trans m6)) (fun a ha => ?_) (by simp only [Int.add_zero, Int.zero_add])
    rw [ht] at ha
    simpa only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or, or_assoc, or_self] using ha
  have hcoinApart : ∀ x ∈ coinT j, x ≠ pool := by
    match j with
    | 0 => decide
    | 1 => decide
    | 2 => decide
  have hTo : ∀ x ∈ coinT j, x ∉ Tn ++ [pool] := fun x hx hm => by
    rcases List.mem_append.1 hm with h | h
    · exact hT x hx h
    · exact hcoinApart x hx (List.mem_singleton.1 h)
  have hread : ((Mf.write 0xc0 (Bytes.toB256 [0]).toBytes).read (0xb60 : B256).toNat (0x44 : B256).toNat).1 =
      transferSel ++ s.caller.toB256.toBytes ++ (Nat.toB256 dy).toBytes := by
    have h := win.read
    rw [← hMb, ← hMf, g.out] at h
    exact h
  have hsize : (Mf.write 0xc0 (Bytes.toB256 [0]).toBytes).size = 0xbc0 := by
    have h := win.size
    rw [← hMb, ← hMf] at h
    exact h
  have hdyLt : dy < 2 ^ 256 := by
    obtain ⟨-, -, -⟩ := g.pays
    have hle' := g.pays.1
    have := coinHeld_lt (w := w) (a := pool) (k := j)
    omega
  obtain ⟨d1, m7, st, len⟩ := f.pay j (b := exPushIn s T2) (S := []) (M := Mf.write 0xc0 (Bytes.toB256 [0]).toBytes)
    (t := (lockedStor w).get kC) (by rw [hkC]; exact g.coinJ) mTo hTo g.named hread hdyLt g.pays.1 g.pays.2.1 g.pays.2.2
  obtain ⟨pD, hpD⟩ : ∃ pD, pD = swapPushD s ((lockedStor w).get kC) j := ⟨_, rfl⟩
  obtain ⟨pN, hpN⟩ : ∃ pN, pN = swapPushN s ((lockedStor w).get kC) j := ⟨_, rfl⟩
  rw [← hpD] at d1
  rw [← hpN] at m7 st len
  rw [← hkC, ← hpD, ← hpN]
  have hNx : pN (exPushIn s T2) [] (Mf.write 0xc0 (Bytes.toB256 [0]).toBytes) = exPushNext s T2 Mf pN := rfl
  rw [hNx] at m7 st len
  have hTail := mv_rawTail s (exPushNext s T2 Mf pN) [] (exPushNext s T2 Mf pN).memory exPushSite
  have hctT : pool ∉ coinT j := fun h => hcoinApart pool h rfl
  have a7 : At s.currentTarget (kC :: kJ :: kI :: Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1) σ2 (exPushTail s T2 Mf pN) :=
    ((a6.ofMv m7 (by rw [ht]; exact hctT)).ofMv hTail List.not_mem_nil)
  have mAll : Mv ((Tn ++ [pool]) ++ coinT j ++ []) (rn + ((4800 * empties (rawHeld w pool j) dy : Nat) : Int) + 0) p (exPushTail s T2 Mf pN) := (mTo.trans m7).trans hTail
  have cT := mAll.clean f.clean
  have vLock : σ2.get lockW = Bytes.toB256 [1] := by
    rw [hσ2, Stor.get_set_ne _ hdJ, Stor.get_set_ne _ hdI]
    exact Stor.get_set_self _ _ _
  have mLock : lockW ∈ kC :: kJ :: kI :: Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1 := by simp only [List.mem_cons, mL, or_true]
  have hOrigL : (exPushTail s T2 Mf pN).getOrigStorVal s s.currentTarget lockW = 0 := by
    rw [cT.orig, hO0]; exact g.lock
  have hTailEq : rawTailBaseNext s (exPushNext s T2 Mf pN) [] (exPushNext s T2 Mf pN).memory exPushSite = exPushTail s T2 Mf pN := rfl
  have hmin : min (replyLen j) 32 = replyLen j := by
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  refine ⟨?_, ?_⟩
  · have hcost : exBackCost s n M c0 (lockedStor w) B X D amp v pD pN =
        279 + c0 + 3540 + (3906 + costGetY s n amp (exI s).toNat (exJ s).toNat (exXw s X D).toNat (X 0).toNat (X 1).toNat (X 2).toNat) +
        (612 + sloadCost s (aBase s n) (Bytes.toB256 [0x02])) +
        exTailCost s (afterSload s (aBase s n) (Bytes.toB256 [0x02])) (exBackDyMem s M (lockedStor w) X D v) (lockedStor w) B D
          (exDyFee (X (exJ s).toNat) (Nat.toB256 v) ((lockedStor w).get feeSlot))
          (exDyOut (X (exJ s).toNat) (Nat.toB256 v) ((lockedStor w).get feeSlot) (exRate (exJ s).toNat)) pD pN := rfl
    rw [hcost, hF, hO, hY, gA, ← hN, ← hMb, aA.sloadCost_cold n2]
    unfold exTailCost exStoreCost
    rw [hVi, hVj, hIw, hJw, ← hkI, ← hkJ, a2.sloadCost_cold (by simp only [List.mem_cons, not_or]; exact ⟨by decide, n3⟩), cost_credit f1 a3 (mk2 mI) (by omega), ← hB1,
      cost_debit f2 a4 (by simp only [List.mem_cons, mJ, or_true]) hle, ← hT2, ← hMf]
    unfold exPushCost
    rw [hJw, ← hkC, a5'.sloadCost_cold (by
        simp only [List.mem_cons, not_or]
        exact ⟨coin_ne_bal j j hkC hkJ, coin_ne_bal j i hkC hkI, by rw [hkC]; exact coin_ne_3 j, by rw [hkC]; exact coin_ne_2 j, by rw [hkC]; exact nC⟩),
      d1, ext_pushSite hsize, len, hmin, hTailEq, a7.sstoreCost_warm mLock, hOrigL, vLock]
    show _ = _ + (_ + (_ + (2600 + 10 + payG w E j dy) + rawTailCost (replyLen j) + 100))
    have hV : sstoreValueCost 0 (Bytes.toB256 [1]) (Bytes.toB256 [0]) = 100 := by decide
    rw [hV]
  · rintro D' ⟨b', l, S', M', G', hb, rfl⟩
    rw [← hN, ← hMb, ← hT2, ← hMf] at hb
    have hb' := hb.symm
    have mb := mAll.congr hb'
    have cb := mb.clean f.clean
    have ab := a7.congr_gas hb'
    have hLog := mv_addLog b' l
    have hcl := hLog.clean cb
    have aL : At s.currentTarget (kC :: kJ :: kI :: Bytes.toB256 [3] :: Bytes.toB256 [0x02] :: K1) σ2 (b'.addLog l) := ⟨ab.keys, ab.stor⟩
    have hR := lock_restore (s := s) (b := b'.addLog l) hg (by rw [hcl.orig, hO0]; exact g.lock) (by rw [aL.val]; exact vLock)
    refine ⟨?_, ?_, ?_⟩
    · have hm := (mb.trans hLog).trans hR
      refine Mv.st (Mv.cast hm (fun a ha => ?_) (by simp only [Int.add_zero])) S' M' G'
      rw [ht] at ha
      have ha' : a ∈ Tn ∨ a = pool ∨ a ∈ coinT j ∨ a = pool := by
        simpa only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or, or_assoc] using ha
      rcases ha' with h | h | h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons.2 (Or.inl h))
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      · exact List.mem_append_right _ (List.mem_cons.2 (Or.inl h))
    · rw [St_getStor, ← ht]
      have := (aL.sstore lockW (Bytes.toB256 [0])).stor
      rw [this, hσ2]
      unfold swapStored
      rw [hkI, hkJ]
    · have hne : s.currentTarget ≠ coinAt j := by
        rw [ht]; exact Ne.symm (coin_ne_pool j)
      rw [St_getStor, afterSstore_getStor_ne _ _ _ _ _ hne, Devm.addLog_getStor, hb.getStor_eq,
        (hTail.same (coinAt j) List.not_mem_nil).stor]
      exact st

end Head

end Blanc.Composition.Curve3PoolPublic
