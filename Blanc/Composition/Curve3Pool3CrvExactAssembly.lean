import Blanc.Composition.Curve3Pool3CrvHeadlines
import Blanc.Composition.Curve3PoolCalleeExactProfiles
import Blanc.Lift.Curve3Pool.HistoryLiveExact

/-!
# Curve 3pool composed with 3Crv: the exact call data and premises from 3Crv's code

The four pool entries that call 3Crv (`remove_liquidity`, `add_liquidity`,
`remove_liquidity_imbalance`, `remove_liquidity_one_coin`) take their exact call data as
`RLExactCalls`/`ALExactCalls`/`RLIExactCalls`/`OCExactCalls`. Here the 3Crv parts of that data
are 3Crv's own named profiles (`c3crv_supplyProfile`, `c3crv_mintProfile`, `c3crv_burnProfile`:
`supplyDebit`/`supplyNext`, `mutDebit`/`mutNext` at each entry's window), so they are closed
functions of the frame's static machine and entry; only the coin calls' debit and successor stay
parameters, given with the coins' own exact profiles (honest environment premises).

* `rlC3Calls`, `alC3Calls`, `rliC3Calls`, `ocC3Calls`: the call data;
* `rlC3W`, `alC3W`, `rliC3W`: the world chains (3Crv's storage at the entry before its
  state-changing call and the model's result after, the caller's coin chain `V`);
* `rlExactPremises_c3crv`, `alExactPremises_c3crv`, `rliExactPremises_c3crv`,
  `ocExactPremises_c3crv`: the exact premise bundles, with no 3Crv premise left beyond the facts
  the bounded composed theorems use (`C3Ready`, supply `T`, `BurnFits`/`MintFits`).
-/

namespace Blanc.Composition.Curve3Pool3CrvExactAssembly

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCalleeExactProfiles
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3At C3With C3Blind c3With_wClosed c3With_keep
  c3At_burn c3At_mint precomp_false)

/-- The pool's token word at the frame's entry. -/
abbrev tokW (sevm : Sevm) (pre : Devm) : B256 := (pre.getStor sevm.currentTarget).get tokenSlot

/-! ## `remove_liquidity` -/

/-- `remove_liquidity`'s exact call data with 3Crv's `totalSupply()` (window `0x17c`/`0x1c0`)
and `burnFrom` (window `0x61c`/`0x6a0`) profiles; the coin pushes are `pushD`/`pushN`. -/
noncomputable def rlC3Calls (sevm : Sevm) (pre : Devm) (pushD : Nat → Devm → List B256 → Mem → Nat)
    (pushN : Nat → Devm → List B256 → Mem → Devm) : RLExactCalls where
  supplyDebit := supplyDebit sevm (tokW sevm pre) 0x17c 0x1c0
  supplyNext := supplyNext sevm (tokW sevm pre) 0x17c 0x1c0
  pushDebit := pushD
  pushNext := pushN
  burnDebit := mutDebit Curve3Crv.burnBodyCost 8 sevm (tokW sevm pre) 0x61c 0x6a0
  burnNext := mutNext Curve3Crv.burnBodyCost Curve3Crv.t_0644_c0 sevm (tokW sevm pre) 0x61c 0x6a0

/-- `remove_liquidity`'s world chain: 3Crv's entry storage `σ` up to the burn and `σb` after. -/
def rlC3W (c3 : Adr) (σ σb : Stor) (V : Nat → Devm → Prop) : Nat → Devm → Prop
  | 4 => C3With c3 σb (V 3)
  | j => C3With c3 σ (V j)

/-- **`remove_liquidity`'s exact premises from 3Crv's code.** -/
theorem rlExactPremises_c3crv {sevm : Sevm} {pre : Devm} {c3 : Adr} {T : B256}
    {V : Nat → Devm → Prop} {U : Nat} {pushD : Nat → Devm → List B256 → Mem → Nat}
    {pushN : Nat → Devm → List B256 → Mem → Devm}
    (ht : (tokW sevm pre).toAdr = c3) (hne : sevm.currentTarget ≠ c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (htok : ¬ sevm.benvStat.rules.isPrecomp c3) (hU : 70000 ≤ U)
    (hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
    (hburn : BurnFits (Devm.getStor pre c3) sevm.currentTarget sevm.caller.toB256 (rlAmt sevm))
    (hVs : ∀ k, C3Blind c3 (V k))
    (hpush : ∀ i, i < 3 → MutableCallProfile sevm (C3With c3 (Devm.getStor pre c3) (V i))
      (C3With c3 (Devm.getStor pre c3) (V (i + 1))) (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++
        (balAt (pre.getStor sevm.currentTarget) i * rlAmt sevm / T).toBytes)
      RawCallOk U 0x520 0x44 0x5c0 (pushD i) (pushN i)) :
    RLExactPremises sevm pre T (rlC3W c3 (Devm.getStor pre c3)
      (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (rlAmt sevm)) V) U
      (rlC3Calls sevm pre pushD pushN) := by
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · exact c3crv_supplyProfile hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep (hVs 0) hb hs hc)
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hpush 0 (by decide)
    · exact hpush 1 (by decide)
    · exact hpush 2 (by decide)
  · refine c3crv_burnProfile hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, hb.1.2]
      exact ⟨hb.1.1, fun h => hne h.symm, hburn⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, hVs 3 b d hb.2 ho hc⟩

/-! ## `add_liquidity` -/

/-- `add_liquidity`'s exact call data with 3Crv's `totalSupply()` (window `0x27c`/`0x2c0`) and
`mint` (window `0xc7c`/`0xd00`) profiles; the coin pulls and the fee coin's two balance reads
are parameters. -/
noncomputable def alC3Calls (sevm : Sevm) (pre : Devm) (pullD : Nat → Devm → List B256 → Mem → Nat)
    (pullN : Nat → Devm → List B256 → Mem → Devm) (balBD balAD : Devm → List B256 → Mem → Nat)
    (balBN balAN : Devm → List B256 → Mem → Devm) : ALExactCalls where
  supplyDebit := supplyDebit sevm (tokW sevm pre) 0x27c 0x2c0
  supplyNext := supplyNext sevm (tokW sevm pre) 0x27c 0x2c0
  pullDebit := pullD
  pullNext := pullN
  balBDebit := balBD
  balBNext := balBN
  balADebit := balAD
  balANext := balAN
  mintDebit := mutDebit Curve3Crv.mintBodyCost 7 sevm (tokW sevm pre) 0xc7c 0xd00
  mintNext := mutNext Curve3Crv.mintBodyCost Curve3Crv.t_056e_c0 sevm (tokW sevm pre) 0xc7c 0xd00

/-- `add_liquidity`'s world chain: 3Crv's entry storage `σ` up to the mint and `σm` after. -/
def alC3W (c3 : Adr) (σ σm : Stor) (V : Nat → Devm → Prop) : Nat → Devm → Prop
  | 4 => C3With c3 σm (V 3)
  | j => C3With c3 σ (V j)

/-- **`add_liquidity`'s exact premises from 3Crv's code.** -/
theorem alExactPremises_c3crv {sevm : Sevm} {pre : Devm} {c3 : Adr} {T B1 B2 mint : B256}
    {V : Nat → Devm → Prop} {U : Nat} {pullD : Nat → Devm → List B256 → Mem → Nat}
    {pullN : Nat → Devm → List B256 → Mem → Devm} {balBD balAD : Devm → List B256 → Mem → Nat}
    {balBN balAN : Devm → List B256 → Mem → Devm}
    (ht : (tokW sevm pre).toAdr = c3) (hne : sevm.currentTarget ≠ c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (htok : ¬ sevm.benvStat.rules.isPrecomp c3) (hU : 70000 ≤ U)
    (hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
    (hmint : MintFits (Devm.getStor pre c3) sevm.currentTarget sevm.caller.toB256 mint)
    (hVs : ∀ k, C3Blind c3 (V k))
    (hpull : ∀ k, k < 3 → alAmt sevm k ≠ 0 →
      MutableCallProfile sevm (C3With c3 (Devm.getStor pre c3) (V k))
        (C3With c3 (Devm.getStor pre c3) (V (k + 1))) (coinAt (pre.getStor sevm.currentTarget) k)
        (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
          (alAmt sevm k).toBytes) RawCallOk U 0x760 0x64 0x820 (pullD k) (pullN k))
    (hbalB : alAmt sevm 2 ≠ 0 →
      StaticWordCallProfile sevm (C3With c3 (Devm.getStor pre c3) (V 2))
        (C3With c3 (Devm.getStor pre c3) (V 2)) (coinAt (pre.getStor sevm.currentTarget) 2)
        (balanceOfData sevm.currentTarget) B1 U 0x53c 0x24 0x5a0 balBD balBN)
    (hbalA : alAmt sevm 2 ≠ 0 →
      StaticWordCallProfile sevm (C3With c3 (Devm.getStor pre c3) (V 3))
        (C3With c3 (Devm.getStor pre c3) (V 3)) (coinAt (pre.getStor sevm.currentTarget) 2)
        (balanceOfData sevm.currentTarget) B2 U 0x87c 0x24 0x8e0 balAD balAN) :
    ALExactPremises sevm (pre.getStor sevm.currentTarget) T B1 B2 mint
      (alC3W c3 (Devm.getStor pre c3) (mintStor (Devm.getStor pre c3) sevm.caller.toB256 mint) V)
      U (alC3Calls sevm pre pullD pullN balBD balAD balBN balAN) := by
  refine ⟨?_, fun k hk hz => ?_, hbalB, hbalA, ?_⟩
  · exact c3crv_supplyProfile hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep (hVs 0) hb hs hc)
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact hpull 0 (by decide) hz
    · exact hpull 1 (by decide) hz
    · exact hpull 2 (by decide) hz
  · refine c3crv_mintProfile hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, hb.1.2]
      exact ⟨hb.1.1, fun h => hne h.symm, hmint⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_mint hb.1 hs hc, hVs 3 b d hb.2 ho hc⟩

/-! ## `remove_liquidity_imbalance` -/

/-- `remove_liquidity_imbalance`'s exact call data with 3Crv's `totalSupply()` (window
`0x17c`/`0x1c0`) and `burnFrom` (window `0x85c`/`0x8e0`) profiles; the coin pushes are
`pushD`/`pushN`. -/
noncomputable def rliC3Calls (sevm : Sevm) (pre : Devm)
    (pushD : Nat → Devm → List B256 → Mem → Nat) (pushN : Nat → Devm → List B256 → Mem → Devm) :
    RLIExactCalls where
  supplyDebit := supplyDebit sevm (tokW sevm pre) 0x17c 0x1c0
  supplyNext := supplyNext sevm (tokW sevm pre) 0x17c 0x1c0
  burnDebit := mutDebit Curve3Crv.burnBodyCost 8 sevm (tokW sevm pre) 0x85c 0x8e0
  burnNext := mutNext Curve3Crv.burnBodyCost Curve3Crv.t_0644_c0 sevm (tokW sevm pre) 0x85c 0x8e0
  pushDebit := pushD
  pushNext := pushN

/-- `remove_liquidity_imbalance`'s world chain: 3Crv's entry storage `σ` before the burn (the
first call after the supply read) and `σb` after, the coin chain `V k` before coin `k`'s
push. -/
def rliC3W (c3 : Adr) (σ σb : Stor) (V : Nat → Devm → Prop) : Nat → Devm → Prop
  | 0 => C3With c3 σ (V 0)
  | j + 1 => C3With c3 σb (V j)

/-- **`remove_liquidity_imbalance`'s exact premises from 3Crv's code.** -/
theorem rliExactPremises_c3crv {sevm : Sevm} {pre : Devm} {c3 : Adr} {T burn : B256}
    {V : Nat → Devm → Prop} {U : Nat} {pushD : Nat → Devm → List B256 → Mem → Nat}
    {pushN : Nat → Devm → List B256 → Mem → Devm}
    (ht : (tokW sevm pre).toAdr = c3) (hne : sevm.currentTarget ≠ c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (htok : ¬ sevm.benvStat.rules.isPrecomp c3) (hU : 70000 ≤ U)
    (hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
    (hburn : BurnFits (Devm.getStor pre c3) sevm.currentTarget sevm.caller.toB256 burn)
    (hVs : ∀ k, C3Blind c3 (V k))
    (hpush : ∀ k, k < 3 → rliAmt sevm k ≠ 0 →
      MutableCallProfile sevm
        (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 burn) (V k))
        (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 burn) (V (k + 1)))
        ((pre.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 k))
        (transferSel ++ sevm.caller.toB256.toBytes ++ (rliAmt sevm k).toBytes) RawCallOk U 0xaa0
        0x44 0xb40 (pushD k) (pushN k)) :
    RLIExactPremises sevm (pre.getStor sevm.currentTarget) T burn
      (rliC3W c3 (Devm.getStor pre c3) (burnStor (Devm.getStor pre c3) sevm.caller.toB256 burn) V)
      U (rliC3Calls sevm pre pushD pushN) := by
  refine ⟨?_, ?_, fun k hk hz => ?_⟩
  · exact c3crv_supplyProfile hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep (hVs 0) hb hs hc)
  · refine c3crv_burnProfile hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, hb.1.2]
      exact ⟨hb.1.1, fun h => hne h.symm, hburn⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, hVs 0 b d hb.2 ho hc⟩
  · exact hpush k hk hz

/-! ## `remove_liquidity_one_coin` -/

/-- `remove_liquidity_one_coin`'s exact call data with 3Crv's `totalSupply()` (window
`0x2bc`/`0x300`) and `burnFrom` (window `0x31c`/`0x3a0`) profiles; the coin push is
`pushD`/`pushN`. -/
noncomputable def ocC3Calls (sevm : Sevm) (pre : Devm) (pushD : Devm → List B256 → Mem → Nat)
    (pushN : Devm → List B256 → Mem → Devm) : OCExactCalls where
  supplyDebit := supplyDebit sevm (tokW sevm pre) 0x2bc 0x300
  supplyNext := supplyNext sevm (tokW sevm pre) 0x2bc 0x300
  burnDebit := mutDebit Curve3Crv.burnBodyCost 8 sevm (tokW sevm pre) 0x31c 0x3a0
  burnNext := mutNext Curve3Crv.burnBodyCost Curve3Crv.t_0644_c0 sevm (tokW sevm pre) 0x31c 0x3a0
  pushDebit := pushD
  pushNext := pushN

/-- **`remove_liquidity_one_coin`'s exact premises from 3Crv's code**, along the chain
`C3With c3 σ (V 0) → C3With c3 σb (V 0) → C3With c3 σb (V 1)`. -/
theorem ocExactPremises_c3crv {sevm : Sevm} {pre : Devm} {c3 : Adr} {T dy : B256}
    {V : Nat → Devm → Prop} {U : Nat} {pushD : Devm → List B256 → Mem → Nat}
    {pushN : Devm → List B256 → Mem → Devm}
    (ht : (tokW sevm pre).toAdr = c3) (hne : sevm.currentTarget ≠ c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (htok : ¬ sevm.benvStat.rules.isPrecomp c3) (hU : 70000 ≤ U)
    (hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
    (hburn : BurnFits (Devm.getStor pre c3) sevm.currentTarget sevm.caller.toB256 (ocAmt sevm))
    (hVs : C3Blind c3 (V 0))
    (hpush : MutableCallProfile sevm
      (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 0))
      (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1))
      ((pre.getStor sevm.currentTarget).get (coinsBase + ocI sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ dy.toBytes) RawCallOk U 0x540 0x44 0x5e0
      pushD pushN) :
    OCExactPremises sevm pre T dy (C3With c3 (Devm.getStor pre c3) (V 0))
      (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 0))
      (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1)) U
      (ocC3Calls sevm pre pushD pushN) := by
  refine ⟨?_, ?_, hpush⟩
  · exact c3crv_supplyProfile hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep hVs hb hs hc)
  · refine c3crv_burnProfile hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, hb.1.2]
      exact ⟨hb.1.1, fun h => hne h.symm, hburn⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, hVs b d hb.2 ho hc⟩

end Blanc.Composition.Curve3Pool3CrvExactAssembly
