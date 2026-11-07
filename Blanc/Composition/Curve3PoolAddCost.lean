import Blanc.Composition.Curve3PoolAddCoins

/-!
# `add_liquidity`'s named cost is bounded

`al_cost0_le`, `al_cost1_le`: the closed cost, from bounds on the calls' debits, each stage at its worst: every `SLOAD` cold, every `SSTORE`
a fresh write, each `get_D_mem` its 255 Newton iterations. `addCalls_debits`: those bounds for the real coins and 3Crv. `add_cost_le`: the cost is at
most `addCostBound`, which is below EIP-7825's per-transaction cap.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvExactAssembly (alC3Calls tokW)

/-- A bound on `add_liquidity`'s named cost: its worst case, not a measurement. -/
def addCostBound : Nat := 2300000

theorem addCostBound_le_cap : addCostBound ≤ namedCostCap := by decide

section Stages

variable {s : Sevm} {p n : Devm} {σ : Stor} {P : ALExactCalls} {m : Mem}

/-- The call debits' bounds. -/
structure AlDebits (P : ALExactCalls) : Prop where
  supply : ∀ b S M, P.supplyDebit b S M ≤ 5336
  pull : ∀ k b S M, P.pullDebit k b S M ≤ 130000
  balB : ∀ b S M, P.balBDebit b S M ≤ 8047
  balA : ∀ b S M, P.balADebit b S M ≤ 8047
  mint : ∀ b S M, P.mintDebit b S M ≤ 56100

theorem alHeadX_le (s : Sevm) (n : Devm) (k : Nat) (T : B256) : alHeadCostX s n k T ≤ 2329 := by
  have h0 := sloadCost_le_lit s n (coinsBase + Nat.toB256 0)
  have h1 := sloadCost_le_lit s n (coinsBase + Nat.toB256 k)
  unfold alHeadCostX alHeadCost
  split
  · omega
  · split <;> omega

theorem alIt_le (hd : AlDebits P) (k : Nat) (B1 T : B256) (f : Bool) : alItCost s σ P n m k B1 T f ≤ 150000 + 2 * 8047 := by
  have hH := alHeadX_le s n k T
  unfold alItCost
  split
  · unfold alSkipCost
    omega
  · split
    · have hH2 := alHeadX_le s n 2 T
      unfold alFeeCost alFeeLen
      have r := rawTail_min (alFeeCallP s σ P n m B1).returnData.length
      have a := hd.balB (alHB s n 2) [3, 0x4c0] (alFeeMemB s σ m)
      have b := hd.pull 2 (alPullId2 s (alFeeCallB s σ P n m) [] (alFeeMemP s σ P n m B1) 2) [3, 0x4c0] (alPullMemC s (alFeeMemP s σ P n m B1) 2)
      have c := hd.balA (alFeeBaseR s σ P n m B1) [3, 0x4c0] (alFeeMemA s σ P n m B1)
      split <;> omega
    · unfold alPlainCost alPlainLen
      have r := rawTail_min (alPlainCall s σ P n m k).returnData.length
      have b := hd.pull k (alPullId2 s (alHB s n k) [] (alHeadMem s m σ k) k) [3, 0x4c0] (alPullMemC s (alHeadMem s m σ k) k)
      split <;> omega

theorem alLoop_le (hd : AlDebits P) (B1 B2 T : B256) (old : Nat → B256) : alLoopCost s σ P n m B1 B2 T old ≤ 129 + 3 * (150000 + 2 * 8047) := by
  have h0 := alIt_le (s := s) (σ := σ) (P := P) (n := n) (m := alInitMem m old) hd 0 B1 T false
  have h1 := alIt_le (s := s) (σ := σ) (P := P) (n := alLN1 s σ P n m B1 old) (m := alLM1 s σ P n m B1 B2 old) hd 1 B1 T (if alAmt s 0 = 0 then false else true)
  have h2 := alIt_le (s := s) (σ := σ) (P := P) (n := alLN2 s σ P n m B1 B2 old) (m := alLM2 s σ P n m B1 B2 old) hd 2 B1 T (if alAmt s 0 = 0 ∧ alAmt s 1 = 0 then false else true)
  unfold alLoopCost
  split <;> omega

theorem alTail_le (hd : AlDebits P) (M : Mem) (mint : B256) : alTailCost s P n M mint ≤ 3566 + 2100 + 56100 + 22100 := by
  have a := sloadCost_le_lit s n tokenSlot
  have b := hd.mint (afterSload s n tokenSlot) [] (alMintMem s M mint)
  have c := sstoreCost_le_lit s (P.mintNext (afterSload s n tokenSlot) [] (alMintMem s M mint)) lockSlot 0
  unfold alTailCost
  omega

theorem alFront_le (hd : AlDebits P) (amp : Nat) : alFrontCost s p P amp ≤ 55200 := by
  unfold alFrontCost alPreCost1 alPreCost2
  have hs := sloadCost_le_lit s
  have ht := sstoreCost_le_lit s
  have ha := Blanc.Composition.Curve3PoolPublic.aGas_le s (alPreBaseA s p)
  have a1 := hs p (Bytes.toB256 [255, 255, 255])
  have a2 := ht (afterSload s p (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])
  have a3 := hs (afterSstore s (afterSload s p (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])
  have a4 := hs (afterSload s (afterSstore s (afterSload s p (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])) (Bytes.toB256 [2])
  have a5 := hs (afterSload s (afterSload s (afterSstore s (afterSload s p (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])) (Bytes.toB256 [2])) (Bytes.toB256 [3])
  have a6 := hs (aBase s (alPreBaseA s p)) (Bytes.toB256 [5])
  have d := hd.supply (alSupBase s p) [] (alSupMem s p (alMv s) (p.getStor s.currentTarget) amp)
  have b1 := hs (alSupNext s p P amp) balancesBase
  have b2 := hs (afterSload s (alSupNext s p P amp) balancesBase) (balancesBase + Bytes.toB256 [1])
  have b3 := hs (afterSload s (afterSload s (alSupNext s p P amp) balancesBase) (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2])
  omega

theorem alFeeIt_le (D0 D1 B N : B256) (c12 : Nat) : alFeeItCost c12 D0 D1 B N ≤ 1047 + c12 := by
  unfold alFeeItCost
  split <;> omega

theorem alD1c0_le (s : Sevm) : alD1c0 s ≤ 29 := by
  unfold alD1c0
  split <;> omega

theorem alStore0_le (s : Sevm) (b : Devm) (nv : Nat → B256) : alStore0Cost s b nv ≤ 110 + 3 * 22100 := by
  have h0 := sstoreCost_le_lit s b balancesBase (nv 0)
  have h1 := sstoreCost_le_lit s (afterSstore s b balancesBase (nv 0)) (balancesBase + Bytes.toB256 [1]) (nv 1)
  have h2 := sstoreCost_le_lit s (afterSstore s (afterSstore s b balancesBase (nv 0)) (balancesBase + Bytes.toB256 [1]) (nv 1)) (balancesBase + Bytes.toB256 [2]) (nv 2)
  unfold alStore0Cost
  omega

theorem alFeeLoop_le (s : Sevm) (b : Devm) (D0 D1 : B256) (old nv : Nat → B256) (s0 s1 s2 : B256) :
    alFeeLoopCost s b D0 D1 old nv s0 s1 s2 ≤ 3 * 1100 + 3 * 22100 := by
  have h0 := sstoreCost_le_lit s b (balancesBase + Nat.toB256 0) s0
  have h1 := sstoreCost_le_lit s (afterSstore s b (balancesBase + Nat.toB256 0) s0) (balancesBase + Nat.toB256 1) s1
  have h2 := sstoreCost_le_lit s (afterSstore s (afterSstore s b (balancesBase + Nat.toB256 0) s0) (balancesBase + Nat.toB256 1) s1) (balancesBase + Nat.toB256 2) s2
  have i0 := alFeeIt_le D0 D1 (old 0) (nv 0) (6 + 7)
  have i1 := alFeeIt_le D0 D1 (old 1) (nv 1) (3 + 3)
  have i2 := alFeeIt_le D0 D1 (old 2) (nv 2) (3 + 3)
  unfold alFeeLoopCost
  omega

theorem alBack0_le (hd : AlDebits P) (M : Mem) (c0 : Nat) (hc : c0 ≤ 29) (A : B256) (nv : Nat → B256) (xb : V3) (v1 : Nat) :
    alBack0Cost s P n M c0 A nv xb v1 ≤ 9000 + 517397 + (110 + 3 * 22100) + (3566 + 2100 + 56100 + 22100) := by
  have hD := costGetDMem_le xb A.toNat
  have hS := alStore0_le s n nv
  have hT := alTail_le (s := s) (P := P) (n := alStore0Base s n nv) hd (alBack0Mem M A nv xb v1) (Nat.toB256 v1)
  unfold alBack0Cost
  omega

theorem alBack1_le (hd : AlDebits P) (M : Mem) (c0 : Nat) (hc : c0 ≤ 29) (A D0 T : B256) (old nv : Nat → B256) (xb xc : V3) (v1 v2 : Nat) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256) :
    alBack1Cost s P n M c0 A D0 T old nv xb xc v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 ≤
      20000 + 2 * 517397 + (3 * 1100 + 3 * 22100) + (3566 + 2100 + 56100 + 22100) := by
  have h1 := costGetDMem_le xb A.toNat
  have h2 := costGetDMem_le xc A.toNat
  have hF := alFeeLoop_le s n D0 (Nat.toB256 v1) old nv s0 s1 s2
  have hT := alTail_le (s := s) (P := P) (n := alFeeLoopBase s n s0 s1 s2) hd (alBack1Mem M A D0 T old nv xb xc v1 v2 f0 f1 f2 x0 x1 x2) (alMintW T D0 (Nat.toB256 v2))
  unfold alBack1Cost
  omega

/-- **The first deposit's closed cost, from the debits.** -/
theorem al_cost0_le (hd : AlDebits P) (amp : Nat) (B1 B2 : B256) (xb : V3) (v1 : Nat) : alExactCost0 s p P amp B1 B2 xb v1 ≤ addCostBound := by
  have hb : addCostBound = 2300000 := rfl
  have hF := alFront_le (s := s) (p := p) hd amp
  have hL := alLoop_le (s := s) (σ := alLocked1 (p.getStor s.currentTarget)) (P := P) (n := alFN1 s p P amp) (m := alFM1 s p P amp 0) hd B1 B2 0 (alOld (p.getStor s.currentTarget))
  have hB := alBack0_le (s := s) (P := P) (n := alLN3 s (alLocked1 (p.getStor s.currentTarget)) P (alFN1 s p P amp) (alFM1 s p P amp 0) B1 B2 (alOld (p.getStor s.currentTarget))) hd
    (alLM3 s (alLocked1 (p.getStor s.currentTarget)) P (alFN1 s p P amp) (alFM1 s p P amp 0) B1 B2 (alOld (p.getStor s.currentTarget))) (alD1c0 s) (alD1c0_le s) (Nat.toB256 amp)
    (alLiveNew s (alOld (p.getStor s.currentTarget)) B1 B2) xb v1
  rw [hb]
  unfold alExactCost0
  omega

/-- **A deposit's closed cost on a positive supply, from the debits.** -/
theorem al_cost1_le (hd : AlDebits P) (amp : Nat) (T B1 B2 : B256) (xa xb xc : V3) (v0 v1 v2 : Nat) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256) :
    alExactCost1 s p P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 ≤ addCostBound := by
  have hb : addCostBound = 2300000 := rfl
  have hF := alFront_le (s := s) (p := p) hd amp
  have hD := costGetDMem_le xa amp
  have hL := alLoop_le (s := s) (σ := alLocked1 (p.getStor s.currentTarget)) (P := P) (n := alFN1 s p P amp) (m := alFM0 s p P amp T xa v0) hd B1 B2 T (alOld (p.getStor s.currentTarget))
  have hB := alBack1_le (s := s) (P := P) (n := alLN3 s (alLocked1 (p.getStor s.currentTarget)) P (alFN1 s p P amp) (alFM0 s p P amp T xa v0) B1 B2 (alOld (p.getStor s.currentTarget))) hd
    (alLM3 s (alLocked1 (p.getStor s.currentTarget)) P (alFN1 s p P amp) (alFM0 s p P amp T xa v0) B1 B2 (alOld (p.getStor s.currentTarget))) (alD1c0 s) (alD1c0_le s) (Nat.toB256 amp) (Nat.toB256 v0) T
    (alOld (p.getStor s.currentTarget)) (alLiveNew s (alOld (p.getStor s.currentTarget)) B1 B2) xb xc v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2
  rw [hb]
  unfold alExactCost1
  omega

end Stages

/-! ## The real coins and 3Crv -/

/-- The debit of a call whose body costs at most `C`, at a window within `4096`. -/
theorem coinDebit_le {g : Sevm → Devm → Nat} {C : Nat} (hg : ∀ s b, s.data.length ≤ 100 → g s b ≤ C) (e : Sevm) (t : B256) (b : Devm) (S : List B256) (M : Mem) :
    coinDebit g e t 0x760 0x64 0x820 b S M ≤ 3016 + C := by
  have ha : acc (b.withGasLeft 0) t ≤ 2600 := acc_le
  have he : ext (b.withGasLeft 0) S M 0x760 0x64 0x820 0x20 ≤ 416 := ext_le (by decide) (by decide)
  have hl : (initSevm (callMsg0 e (b.withGasLeft 0) S M 0 t 0x760 0x64 0x820 0x20)).data.length ≤ 100 := by
    rw [callMsg0_data, mem_read_len]; decide
  have := hg _ (initDevm (callMsg0 e (b.withGasLeft 0) S M 0 t 0x760 0x64 0x820 0x20)) hl
  unfold coinDebit
  omega

theorem addPullD_le (e : Sevm) (d : Devm) (k : Nat) (b : Devm) (S : List B256) (M : Mem) : addPullD e d k b S M ≤ 130000 := by
  match k with
  | 0 =>
    have := coinDebit_le (g := Dai.pullG) (C := 88000) (fun s b _ => Dai.pullG_le s b) e (coinW e d 0) b S M
    exact Nat.le_trans this (by decide)
  | 1 =>
    have := coinDebit_le (g := UsdcLive.pullG) (C := 102000 + 8300) (fun s b hl => UsdcLive.proxyG_le (w := 1) (impl := UsdcLive.implPullG) (Cu := 102000) hl (by
      have h := UsdcLive.pullW_le (sevm := initSevm (UsdcLive.dMsg s b 0)) (b := initDevm (UsdcLive.dMsg s b 0))
      rwa [UsdcLive.pullW_eq] at h)) e (coinW e d 1) b S M
    exact Nat.le_trans this (by decide)
  | _ + 2 =>
    have := coinDebit_le (g := Usdt.pullG) (C := 122180) (fun s b _ => by
      have h := Usdt.pullW_le (sevm := s) (b := b)
      rwa [Usdt.pullW_eq] at h) e (coinW e d 2) b S M
    exact Nat.le_trans this (by decide)

/-- **The real coins' and 3Crv's debits are bounded.** -/
theorem addCalls_debits (e : Sevm) (d : Devm) : AlDebits (addCalls e d) where
  supply := fun b S M => Blanc.Composition.Curve3PoolCalleeExactProfiles.supplyDebit_le (by decide) (by decide) b S M
  pull := addPullD_le e d
  balB := fun b S M => Curve3PoolUsdt.usdt_balDebit_le (by decide) (by decide) b S M
  balA := fun b S M => Curve3PoolUsdt.usdt_balDebit_le (by decide) (by decide) b S M
  mint := fun b S M => by
    show Curve3PoolCalleeExactProfiles.mutDebit Curve3Crv.mintBodyCost 7 e (tokW e d) 0xc7c 0xd00 b S M ≤ _
    unfold Curve3PoolCalleeExactProfiles.mutDebit Curve3PoolCalleeExactProfiles.mutBodyCost
    have h1 : acc (b.withGasLeft 0) (tokW e d) ≤ 2600 := acc_le
    have h2 : ext (b.withGasLeft 0) S M 0xc7c 0x44 0xd00 0x20 ≤ 416 := ext_le (by decide) (by decide)
    have h3 := Curve3PoolCalleeExactProfiles.mintBodyCost_le (initSevm (callMsg0 e (b.withGasLeft 0) S M 0 (tokW e d) 0xc7c 0x44 0xd00 0x20))
      (initDevm (callMsg0 e (b.withGasLeft 0) S M 0 (tokW e d) 0xc7c 0x44 0xd00 0x20))
    have h4 : Curve3Crv.dispatchGas 7 ≤ 400 := by decide
    omega

end Blanc.Composition.Curve3PoolPublic
