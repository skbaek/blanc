import Blanc.Composition.Curve3Pool3CrvLiveWitness
import Blanc.Composition.Curve3Pool3CrvCoinExact
import Blanc.Composition.Curve3Pool3CrvExactAssembly

/-!
# The exact-gas premises are satisfiable by `Token20` coins and the deployed 3Crv

The exact twins of `Curve3Pool3CrvLiveWitness.lean`: each entry's exact premise bundle
(`RLExactPremises`, `ALExactPremises`, `RLIExactPremises`, `OCExactPremises`, and `exchange`'s three
exact profiles) holds at `U = 80000` for some call data `P`, along the same world chains, with
coins running `Token20` (`token20_coinPushExactAt`, `token20_coinPullExactAt`,
`token20_coinBalExactAt`) and the deployed 3Crv's named profiles (`c3crv_supplyProfile`,
`c3crv_mintProfile`, `c3crv_burnProfile`). As there, only the callee premises are proved: the
model step at the entry is not discharged and the amounts are not tied to the model's outputs.

`<entry>_exactPremises_satisfiable`: the chain's closedness, its entry world, and `∃ P` with the
exact bundle.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCalleeExactProfiles
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3At c3At_burn c3At_mint precomp_false)

/-! ## `remove_liquidity` -/

/-- **`removeLiquidity_live_exact`'s premises are satisfiable** along `rlWorld` at
`U = 80000`. -/
theorem removeLiquidity_exactPremises_satisfiable {sevm : Sevm} {pre : Devm} {T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256
      (rlAmt sevm))
    (hfits : ∀ k : Fin 3, T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget
      sevm.caller (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T)) :
    (∀ k, k ≤ 3 → WClosed sevm (rlWorld sevm pre k)) ∧ rlWorld sevm pre 0 pre ∧
      ∃ P : RLExactCalls, RLExactPremises sevm pre T (rlWorld sevm pre) 80000 P := by
  obtain ⟨hcl, h0, -⟩ := removeLiquidity_premises_satisfiable hfork hstatic hdepth hc3 hcoins
    hburn hfits
  have e0 : ∀ n, n ≤ 3 → (if 4 ≤ n then burnStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 (rlAmt sevm) else Devm.getStor pre (tokOf sevm pre)) =
      Devm.getStor pre (tokOf sevm pre) := fun n hn => ite_eq_right (by omega)
  have hpush : ∀ k : Fin 3, CoinPushExactAt sevm (rlWorld sevm pre k) (rlWorld sevm pre (k + 1))
      ((pre.getStor sevm.currentTarget).get (coinSlot k))
      (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) 80000 0x520 0x5c0 := by
    intro k
    refine token20_coinPushExactAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2 k (le_refl _)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => ?_⟩)
    · rw [(hb.2 k (le_refl _)).2]; exact hfits k
    · have h1 := hb.1
      rw [e0 _ (by omega)] at h1
      rw [e0 _ (by omega)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok k))) hl.code
    · exact coinPinned_keep (hb.2 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code
  obtain ⟨d0, n0, p0⟩ := hpush 0
  obtain ⟨d1, n1, p1⟩ := hpush 1
  obtain ⟨d2, n2, p2⟩ := hpush 2
  refine ⟨hcl, h0, ⟨supplyDebit sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x17c 0x1c0,
    supplyNext sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x17c 0x1c0,
    fun i => if i = 0 then d0 else if i = 1 then d1 else d2,
    fun i => if i = 0 then n0 else if i = 1 then n1 else n2,
    mutDebit Curve3Crv.burnBodyCost 8 sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x61c
      0x6a0,
    mutNext Curve3Crv.burnBodyCost Curve3Crv.t_0644_c0 sevm
      ((pre.getStor sevm.currentTarget).get tokenSlot) 0x61c 0x6a0⟩, ?_, fun i hi => ?_, ?_⟩
  · exact c3crv_supplyProfile hfork hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2, e0 0 (by decide)]; exact hc3.supply⟩)
      (fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc,
        fun j hj => coinPinned_keep (hb.2 j hj) (hs _) hc⟩)
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
  · refine c3crv_burnProfile hfork hstatic hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) ?_ ?_
    · intro b hb
      exact ⟨hb.1.1, hc3.pool, by rw [hb.1.2, e0 3 (by decide)]; exact hburn⟩
    · intro b d hb _ hs hc
      refine ⟨⟨(hc _).trans hb.1.1, ?_⟩, fun j hj => absurd j.isLt (by omega)⟩
      rw [hs, hb.1.2, e0 3 (by decide), ite_eq_left (by decide)]

/-! ## `add_liquidity` -/

/-- **`addLiquidity_live_exact`'s premises are satisfiable** along `alWorld` at `U = 80000`
(the fee coin's two `balanceOf(self)` answers are its ledger before and after its pull). -/
theorem addLiquidity_exactPremises_satisfiable {sevm : Sevm} {pre : Devm} {T m : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hmint : MintFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m)
    (hfits : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → T20PullFits (pre.getStor (coinOf sevm pre k))
      sevm.caller sevm.currentTarget sevm.currentTarget (alAmt sevm k.val)) :
    (∀ k, k ≤ 4 → WClosed sevm (alWorld sevm pre m k)) ∧ alWorld sevm pre m 0 pre ∧
      (∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, alWorld sevm pre m k b →
        alWorld sevm pre m (k + 1) b) ∧
      ∃ P : ALExactCalls, ALExactPremises sevm (pre.getStor sevm.currentTarget) T
        ((pre.getStor (coinOf sevm pre 2)).get
          (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget))
        ((alFeeStor sevm pre).get (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget))
        m (alWorld sevm pre m) 80000 P := by
  obtain ⟨hcl, h0, -, -, hskip, -, -⟩ := addLiquidity_premises_satisfiable hfork hstatic hdepth
    hc3 hcoins hmint hfits
  have e0 : ∀ n, n ≤ 3 → (if 4 ≤ n then mintStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) =
      Devm.getStor pre (tokOf sevm pre) := fun n hn => ite_eq_right (by omega)
  have keep : ∀ k b d, alWorld sevm pre m k b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → alWorld sevm pre m k d :=
    fun k b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc,
      fun j hj => coinPinned_keep (hb.2.1 j hj) (hs _) hc,
      fun h3 ha => ⟨(hc _).trans (hb.2.2 h3 ha).1, (hs _).trans (hb.2.2 h3 ha).2⟩⟩
  -- the pulls of the two non-fee coins
  have hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
      CoinPullExactAt sevm (alWorld sevm pre m k) (alWorld sevm pre m (k + 1))
        ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) 80000 0x760
        0x820 := by
    intro k hk ha
    have hk2 : k.val ≠ 2 := fun h => hk (Fin.ext h)
    refine token20_coinPullExactAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2.1 k (le_refl _)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => ?_, fun h3 => absurd h3 (by omega)⟩)
    · rw [(hb.2.1 k (le_refl _)).2]; exact hfits k ha
    · have h1 := hb.1
      rw [e0 _ (by omega)] at h1
      rw [e0 _ (by omega)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok k))) hl.code
    · exact coinPinned_keep (hb.2.1 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code
  -- the fee coin's pull and its two balance reads
  have hfee : alAmt sevm 2 ≠ 0 →
      CoinPullExactAt sevm (alWorld sevm pre m 2) (alWorld sevm pre m 3)
        ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (alAmt sevm 2) 80000 0x760 0x820 := by
    intro ha
    refine token20_coinPullExactAt hfork hstatic hdepth (hcoins.prec 2) rfl (hcoins.pool 2)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2.1 2 (le_refl _)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => absurd j.isLt (by omega), fun _ _ => ⟨?_, ?_⟩⟩)
    · rw [(hb.2.1 2 (le_refl _)).2]; exact hfits 2 ha
    · have h1 := hb.1
      rw [e0 2 (by decide)] at h1
      rw [e0 3 (by decide)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok 2))) hl.code
    · exact (hl.code _).trans (hb.2.1 2 (le_refl _)).1
    · rw [hl.stor, (hb.2.1 2 (le_refl _)).2]
  have hbalB : CoinBalExactAt sevm (alWorld sevm pre m 2) (alWorld sevm pre m 2)
      ((pre.getStor sevm.currentTarget).get (coinSlot 2))
      ((pre.getStor (coinOf sevm pre 2)).get
        (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget)) 80000 0x53c 0x5a0 :=
    token20_coinBalExactAt hfork hdepth (hcoins.prec 2) rfl (by decide) (by decide) (by decide)
      (fun b hb => ⟨(hb.2.1 2 (le_refl _)).1, by rw [(hb.2.1 2 (le_refl _)).2]⟩)
      (fun b d hb hs hc => keep 2 b d hb hs hc)
  obtain ⟨dB, nB, pB⟩ := hbalB
  -- the balance after the pull is read only when the fee coin's amount is nonzero
  have hbalA : alAmt sevm 2 ≠ 0 → CoinBalExactAt sevm (alWorld sevm pre m 3)
      (alWorld sevm pre m 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2))
      ((alFeeStor sevm pre).get (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget))
      80000 0x87c 0x8e0 := fun ha =>
    token20_coinBalExactAt hfork hdepth (hcoins.prec 2) rfl (by decide) (by decide) (by decide)
      (fun b hb => ⟨(hb.2.2 rfl ha).1, by rw [(hb.2.2 rfl ha).2]⟩)
      (fun b d hb hs hc => keep 3 b d hb hs hc)
  have hpull' : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 →
      CoinPullExactAt sevm (alWorld sevm pre m k) (alWorld sevm pre m (k + 1))
        ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) 80000 0x760
        0x820 := by
    intro k ha
    by_cases hk : k = feeIndex
    · subst hk; exact hfee ha
    · exact hpull k hk ha
  have hpz : ∀ k : Fin 3, ∃ (d : Devm → List B256 → Mem → Nat)
      (n : Devm → List B256 → Mem → Devm), alAmt sevm k.val ≠ 0 →
      MutableCallProfile sevm (alWorld sevm pre m k) (alWorld sevm pre m (k + 1))
        ((pre.getStor sevm.currentTarget).get (coinSlot k))
        (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
          (alAmt sevm k.val).toBytes) RawCallOk 80000 0x760 0x64 0x820 d n := by
    intro k
    by_cases ha : alAmt sevm k.val = 0
    · exact ⟨fun _ _ _ => 0, fun b _ _ => b, fun h => absurd ha h⟩
    · obtain ⟨d, n, p⟩ := hpull' k ha
      exact ⟨d, n, fun _ => p⟩
  have hAz : ∃ (d : Devm → List B256 → Mem → Nat) (n : Devm → List B256 → Mem → Devm),
      alAmt sevm 2 ≠ 0 →
      StaticWordCallProfile sevm (alWorld sevm pre m 3) (alWorld sevm pre m 3)
        ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (balanceOfData sevm.currentTarget)
        ((alFeeStor sevm pre).get (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget))
        80000 0x87c 0x24 0x8e0 d n := by
    by_cases ha : alAmt sevm 2 = 0
    · exact ⟨fun _ _ _ => 0, fun b _ _ => b, fun h => absurd ha h⟩
    · obtain ⟨d, n, p⟩ := hbalA ha
      exact ⟨d, n, fun _ => p⟩
  obtain ⟨d0, n0, p0⟩ := hpz 0
  obtain ⟨d1, n1, p1⟩ := hpz 1
  obtain ⟨d2, n2, p2⟩ := hpz 2
  obtain ⟨dA, nA, pA⟩ := hAz
  refine ⟨hcl, h0, hskip, ⟨supplyDebit sevm ((pre.getStor sevm.currentTarget).get tokenSlot)
    0x27c 0x2c0, supplyNext sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x27c 0x2c0,
    fun i => if i = 0 then d0 else if i = 1 then d1 else d2,
    fun i => if i = 0 then n0 else if i = 1 then n1 else n2, dB, nB, dA, nA,
    mutDebit Curve3Crv.mintBodyCost 7 sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0xc7c
      0xd00,
    mutNext Curve3Crv.mintBodyCost Curve3Crv.t_056e_c0 sevm
      ((pre.getStor sevm.currentTarget).get tokenSlot) 0xc7c 0xd00⟩,
    ?_, fun k hk ha => ?_, fun _ => pB, pA, ?_⟩
  · exact c3crv_supplyProfile hfork hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2, e0 0 (by decide)]; exact hc3.supply⟩)
      (fun b d hb hs hc => keep 0 b d hb hs hc)
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact p0 ha
    · exact p1 ha
    · exact p2 ha
  · refine c3crv_mintProfile hfork hstatic hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, hc3.pool, by rw [hb.1.2, e0 3 (by decide)]; exact hmint⟩)
      (fun b d hb _ hs hc => ⟨⟨(hc _).trans hb.1.1, ?_⟩, fun j hj => absurd j.isLt (by omega),
        fun h3 => absurd h3 (by decide)⟩)
    rw [hs, hb.1.2, e0 3 (by decide), ite_eq_left (by decide)]

/-! ## `remove_liquidity_imbalance` -/

/-- **`removeLiquidityImbalance_live_exact`'s premises are satisfiable** along `rliWorld` at
`U = 80000`. -/
theorem removeLiquidityImbalance_exactPremises_satisfiable {sevm : Sevm} {pre : Devm}
    {T m : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m)
    (hfits : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → T20MoveFits (pre.getStor (coinOf sevm pre k))
      sevm.currentTarget sevm.caller (rliAmt sevm k.val)) :
    (∀ j, j ≤ 4 → WClosed sevm (rliWorld sevm pre m j)) ∧ rliWorld sevm pre m 0 pre ∧
      (∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, rliWorld sevm pre m (k + 1) b →
        rliWorld sevm pre m (k + 2) b) ∧
      ∃ P : RLIExactCalls, RLIExactPremises sevm (pre.getStor sevm.currentTarget) T m
        (rliWorld sevm pre m) 80000 P := by
  obtain ⟨hcl, h0, -, -, -, hskip⟩ := removeLiquidityImbalance_premises_satisfiable hfork hstatic
    hdepth hc3 hcoins hburn hfits
  have e1 : ∀ n, 1 ≤ n → (if 1 ≤ n then burnStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) =
      burnStor (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256 m := fun n hn => ite_eq_left hn
  have e0 : (if 1 ≤ 0 then burnStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) =
      Devm.getStor pre (tokOf sevm pre) := ite_eq_right (by decide)
  have hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 →
      CoinPushExactAt sevm (rliWorld sevm pre m (k + 1)) (rliWorld sevm pre m (k + 2))
        ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) 80000 0xaa0
        0xb40 := by
    intro k ha
    refine token20_coinPushExactAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2 k (by omega)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => ?_⟩)
    · rw [(hb.2 k (by omega)).2]; exact hfits k ha
    · have h1 := hb.1
      rw [e1 _ (by omega)] at h1
      rw [e1 _ (by omega)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok k))) hl.code
    · exact coinPinned_keep (hb.2 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code
  have hpz : ∀ k : Fin 3, ∃ (d : Devm → List B256 → Mem → Nat)
      (n : Devm → List B256 → Mem → Devm), rliAmt sevm k.val ≠ 0 →
      MutableCallProfile sevm (rliWorld sevm pre m (k + 1)) (rliWorld sevm pre m (k + 2))
        ((pre.getStor sevm.currentTarget).get (coinSlot k))
        (transferSel ++ sevm.caller.toB256.toBytes ++ (rliAmt sevm k.val).toBytes) RawCallOk 80000
        0xaa0 0x44 0xb40 d n := by
    intro k
    by_cases ha : rliAmt sevm k.val = 0
    · exact ⟨fun _ _ _ => 0, fun b _ _ => b, fun h => absurd ha h⟩
    · obtain ⟨d, n, p⟩ := hpush k ha
      exact ⟨d, n, fun _ => p⟩
  obtain ⟨d0, n0, p0⟩ := hpz 0
  obtain ⟨d1, n1, p1⟩ := hpz 1
  obtain ⟨d2, n2, p2⟩ := hpz 2
  refine ⟨hcl, h0, hskip, ⟨supplyDebit sevm ((pre.getStor sevm.currentTarget).get tokenSlot)
    0x17c 0x1c0, supplyNext sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x17c 0x1c0,
    mutDebit Curve3Crv.burnBodyCost 8 sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x85c
      0x8e0,
    mutNext Curve3Crv.burnBodyCost Curve3Crv.t_0644_c0 sevm
      ((pre.getStor sevm.currentTarget).get tokenSlot) 0x85c 0x8e0,
    fun i => if i = 0 then d0 else if i = 1 then d1 else d2,
    fun i => if i = 0 then n0 else if i = 1 then n1 else n2⟩, ?_, ?_, fun k hk ha => ?_⟩
  · exact c3crv_supplyProfile hfork hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2, e0]; exact hc3.supply⟩)
      (fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc,
        fun j hj => coinPinned_keep (hb.2 j hj) (hs _) hc⟩)
  · refine c3crv_burnProfile hfork hstatic hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, hc3.pool, by rw [hb.1.2, e0]; exact hburn⟩)
      (fun b d hb ho hs hc => ⟨⟨(hc _).trans hb.1.1, ?_⟩,
        fun j hj => coinPinned_keep (hb.2 j (by omega)) (ho _ (hcoins.tok j)) hc⟩)
    rw [hs, hb.1.2, e0, e1 1 (le_refl _)]
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact p0 ha
    · exact p1 ha
    · exact p2 ha

/-! ## `remove_liquidity_one_coin` -/

/-- **`removeLiquidityOneCoin_live_exact`'s premises are satisfiable** along `ocWorld` at
3Crv's entry storage, at its burned storage, and `True`, at `U = 80000`. -/
theorem removeLiquidityOneCoin_exactPremises_satisfiable {sevm : Sevm} {pre : Devm} {T v : B256}
    {i : Fin 3} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hi : i.val = (ocI sevm).toNat)
    (hcode : pre.getCode (coinOf sevm pre i) = VyperNonreentrantDeployed.Token20.code)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre i))
    (hpool : coinOf sevm pre i ≠ sevm.currentTarget) (htok : coinOf sevm pre i ≠ tokOf sevm pre)
    (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256
      (ocAmt sevm))
    (hfits : T20MoveFits (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller v) :
    WClosed sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i) ∧
      WClosed sevm (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre))
        sevm.caller.toB256 (ocAmt sevm)) i) ∧
      ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i pre ∧ WClosed sevm (fun _ => True) ∧
      ∃ P : OCExactCalls, OCExactPremises sevm pre T v
        (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256
          (ocAmt sevm)) i) (fun _ => True) 80000 P := by
  obtain ⟨hcl0, hcl1, h0, -, -, hclT, -⟩ := removeLiquidityOneCoin_premises_satisfiable hfork
    hstatic hdepth hc3 hcode hprec hpool htok hburn hfits
  have hci : coinSlot i = coinsBase + ocI sevm := by
    simp only [coinSlot, hi, toB256_toNat]
  obtain ⟨dP, nP, pP⟩ : CoinPushExactAt sevm (ocWorld sevm pre (burnStor
      (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256 (ocAmt sevm)) i) (fun _ => True)
      ((pre.getStor sevm.currentTarget).get (coinSlot i)) v 80000 0x540 0x5e0 :=
    token20_coinPushExactAt hfork hstatic hdepth hprec rfl hpool (le_refl _) (by decide)
      (by decide) (fun b hb => ⟨hb.2.1, by rw [hb.2.2]; exact hfits⟩) (fun _ _ _ _ => trivial)
  rw [hci] at pP
  refine ⟨hcl0, hcl1, h0, hclT, ⟨supplyDebit sevm ((pre.getStor sevm.currentTarget).get tokenSlot)
    0x2bc 0x300, supplyNext sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x2bc 0x300,
    mutDebit Curve3Crv.burnBodyCost 8 sevm ((pre.getStor sevm.currentTarget).get tokenSlot) 0x31c
      0x3a0,
    mutNext Curve3Crv.burnBodyCost Curve3Crv.t_0644_c0 sevm
      ((pre.getStor sevm.currentTarget).get tokenSlot) 0x31c 0x3a0, dP, nP⟩, ?_, ?_, pP⟩
  · exact c3crv_supplyProfile hfork hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2]; exact hc3.supply⟩)
      (fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc, coinPinned_keep hb.2 (hs _) hc⟩)
  · exact c3crv_burnProfile hfork hstatic hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, hc3.pool, by rw [hb.1.2]; exact hburn⟩)
      (fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, coinPinned_keep hb.2 (ho _ htok) hc⟩)

/-! ## `exchange` -/

section Exchange

variable (sevm : Sevm) (pre : Devm)

/-- The input coin's ledger after its pull of `exDx`. -/
abbrev exPulledStor (i : Fin 3) : Stor :=
  t20Move (t20Allow (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget
    (exDx sevm)) sevm.caller sevm.currentTarget (exDx sevm)

/-- `exchange`'s world before the pull: coins `i` and `j` as at the entry. -/
def exWorld0 (i j : Fin 3) (b : Devm) : Prop :=
  CoinPinned sevm pre i b ∧ CoinPinned sevm pre j b

/-- `exchange`'s world between the pull and the push: coin `i` as its pull leaves it, coin `j` as
at the entry. -/
def exWorld1 (i j : Fin 3) (b : Devm) : Prop :=
  (b.getCode (coinOf sevm pre i) = VyperNonreentrantDeployed.Token20.code ∧
    b.getStor (coinOf sevm pre i) = exPulledStor sevm pre i) ∧ CoinPinned sevm pre j b

end Exchange

/-- **`exchange_live_exact`'s premises are satisfiable** with `Token20` coins `i ≠ j` whose
ledgers cover the pull of `exDx` and the push of `v`, along `exWorld0 → exWorld1 → True` at
`U = 80000`; the fee coin's two `balanceOf(self)` answers are coin `i`'s ledger before and after
its pull. -/
theorem exchange_exactPremises_satisfiable {sevm : Sevm} {pre : Devm} {i j : Fin 3} {v : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcoins : T20Coins sevm pre) (hij : i ≠ j)
    (hpullFits : T20PullFits (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget
      sevm.currentTarget (exDx sevm))
    (hpushFits : T20MoveFits (pre.getStor (coinOf sevm pre j)) sevm.currentTarget sevm.caller v) :
    WClosed sevm (exWorld0 sevm pre i j) ∧ WClosed sevm (exWorld1 sevm pre i j) ∧
      WClosed sevm (fun _ => True) ∧ exWorld0 sevm pre i j pre ∧
      ∃ P : ExchangeExactCalls,
        (i = feeIndex →
          StaticWordCallProfile sevm (exWorld0 sevm pre i j) (exWorld0 sevm pre i j)
            ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
            ((pre.getStor (coinOf sevm pre i)).get
              (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget))
            80000 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
          StaticWordCallProfile sevm (exWorld1 sevm pre i j) (exWorld1 sevm pre i j)
            ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
            ((exPulledStor sevm pre i).get
              (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget))
            80000 0x71c 0x24 0x780 P.balD2 P.balN2) ∧
        MutableCallProfile sevm (exWorld0 sevm pre i j) (exWorld1 sevm pre i j)
          ((pre.getStor sevm.currentTarget).get (coinSlot i))
          (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
            (exDx sevm).toBytes) RawCallOk 80000 0x600 0x64 0x6c0 P.pullD P.pullN ∧
        MutableCallProfile sevm (exWorld1 sevm pre i j) (fun _ => True)
          ((pre.getStor sevm.currentTarget).get (coinSlot j))
          (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes) RawCallOk 80000 0xb60 0x44 0xc00
          P.pushD P.pushN := by
  have hcij : coinOf sevm pre j ≠ coinOf sevm pre i := hcoins.apart j i (Ne.symm hij)
  have keep0 : ∀ b d, exWorld0 sevm pre i j b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → exWorld0 sevm pre i j d :=
    fun b d hb hs hc => ⟨coinPinned_keep hb.1 (hs _) hc, coinPinned_keep hb.2 (hs _) hc⟩
  have keep1 : ∀ b d, exWorld1 sevm pre i j b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → exWorld1 sevm pre i j d :=
    fun b d hb hs hc => ⟨⟨(hc _).trans hb.1.1, (hs _).trans hb.1.2⟩, coinPinned_keep hb.2 (hs _) hc⟩
  obtain ⟨dB1, nB1, pB1⟩ : CoinBalExactAt sevm (exWorld0 sevm pre i j) (exWorld0 sevm pre i j)
      ((pre.getStor sevm.currentTarget).get (coinSlot i))
      ((pre.getStor (coinOf sevm pre i)).get
        (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget)) 80000 0x3dc 0x440 :=
    token20_coinBalExactAt hfork hdepth (hcoins.prec i) rfl (by decide) (by decide) (by decide)
      (fun b hb => ⟨hb.1.1, by rw [hb.1.2]⟩) keep0
  obtain ⟨dB2, nB2, pB2⟩ : CoinBalExactAt sevm (exWorld1 sevm pre i j) (exWorld1 sevm pre i j)
      ((pre.getStor sevm.currentTarget).get (coinSlot i))
      ((exPulledStor sevm pre i).get
        (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget)) 80000 0x71c 0x780 :=
    token20_coinBalExactAt hfork hdepth (hcoins.prec i) rfl (by decide) (by decide) (by decide)
      (fun b hb => ⟨hb.1.1, by rw [hb.1.2]⟩) keep1
  obtain ⟨dL, nL, pL⟩ : CoinPullExactAt sevm (exWorld0 sevm pre i j) (exWorld1 sevm pre i j)
      ((pre.getStor sevm.currentTarget).get (coinSlot i)) (exDx sevm) 80000 0x600 0x6c0 :=
    token20_coinPullExactAt hfork hstatic hdepth (hcoins.prec i) rfl (hcoins.pool i) (le_refl _)
      (by decide) (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2]; exact hpullFits⟩)
      (fun b d hb hl => ⟨⟨(hl.code _).trans hb.1.1, by rw [hl.stor, hb.1.2]⟩,
        coinPinned_keep hb.2 (hl.other _ hcij) hl.code⟩)
  obtain ⟨dP, nP, pP⟩ : CoinPushExactAt sevm (exWorld1 sevm pre i j) (fun _ => True)
      ((pre.getStor sevm.currentTarget).get (coinSlot j)) v 80000 0xb60 0xc00 :=
    token20_coinPushExactAt hfork hstatic hdepth (hcoins.prec j) rfl (hcoins.pool j) (le_refl _)
      (by decide) (by decide) (fun b hb => ⟨hb.2.1, by rw [hb.2.2]; exact hpushFits⟩)
      (fun _ _ _ _ => trivial)
  refine ⟨WClosed.of_foreign fun b d hb hs hc =>
      ⟨coinPinned_keep hb.1 (hs _ (hcoins.pool i)) hc, coinPinned_keep hb.2 (hs _ (hcoins.pool j)) hc⟩,
    WClosed.of_foreign fun b d hb hs hc =>
      ⟨⟨(hc _).trans hb.1.1, (hs _ (hcoins.pool i)).trans hb.1.2⟩,
        coinPinned_keep hb.2 (hs _ (hcoins.pool j)) hc⟩,
    WClosed.of_foreign fun _ _ _ _ _ => trivial,
    ⟨⟨hcoins.code i, rfl⟩, ⟨hcoins.code j, rfl⟩⟩,
    ⟨dB1, nB1, dL, nL, dB2, nB2, dP, nP⟩, fun _ => ⟨pB1, pB2⟩, pL, pP⟩

end Blanc.Composition.Curve3Pool3CrvInstance
