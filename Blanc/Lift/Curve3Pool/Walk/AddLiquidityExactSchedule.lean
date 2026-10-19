import Blanc.Lift.Curve3Pool.Walk.AlLiveMint
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityExactSchedule

/-!
# `add_liquidity`, exact: the calls' data and the pull loop's canonical iterations

`ALExactCalls` is data only: the debit and canonical successor of each of `add_liquidity`'s
external calls (3Crv's `totalSupply()`, coin `k`'s `transferFrom`, the fee coin's two
`balanceOf(self)` reads, 3Crv's `mint`). `ALExactPremises` says each pair is an exact profile at
its call window and world step; a pull or a balance read is required only where its amount is
nonzero, as the call is made only there. Both are fixed before any residual gas.

The pull loop's iterations are priced and described at a canonical base `n` and memory `m` by
three shapes, as the stage cores report them (`rx_al_headE`, `rx_al_feeTest`, `rx_al_pullCoreE`
/ `rx_al_pullCore840E`, `rx_al_bal1E`, `rx_al_joinPlain`, `rx_al_joinFeeE`, `rx_al_creditE`, the
loop test): a zero amount (`alSkip…`: the head, the credit, the test), a plain coin's pull
(`alPlain…`) and the fee coin's pull between its two `balanceOf(self)` reads (`alFee…`). The flag
`p` records that an earlier pull already grew the memory to `0x840`; `T` selects the head's
first-deposit or positive-supply path. Every charge is read at a canonical state; none is a bound.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The calls' functions, as data: debit and canonical successor of the `totalSupply()` read, of
coin `k`'s `transferFrom`, of the fee coin's `balanceOf(self)` before and after its pull, and of
the `mint`. -/
structure ALExactCalls where
  supplyDebit : Devm → List B256 → Mem → Nat
  supplyNext : Devm → List B256 → Mem → Devm
  pullDebit : Nat → Devm → List B256 → Mem → Nat
  pullNext : Nat → Devm → List B256 → Mem → Devm
  balBDebit : Devm → List B256 → Mem → Nat
  balBNext : Devm → List B256 → Mem → Devm
  balADebit : Devm → List B256 → Mem → Nat
  balANext : Devm → List B256 → Mem → Devm
  mintDebit : Devm → List B256 → Mem → Nat
  mintNext : Devm → List B256 → Mem → Devm

/-- **The exact premises**: each call an exact profile with the data's functions, at its window
and along the world chain `W 0 → … → W 4`, at the entry storage `σ`. -/
structure ALExactPremises (sevm : Sevm) (σ : Stor) (T B1 B2 mint : B256) (W : Nat → Devm → Prop)
    (U : Nat) (P : ALExactCalls) : Prop where
  supply : StaticWordCallProfile sevm (W 0) (W 0) (σ.get tokenSlot) totalSupplyData T U 0x27c 4
    0x2c0 P.supplyDebit P.supplyNext
  pull : ∀ k, k < 3 → alAmt sevm k ≠ 0 → MutableCallProfile sevm (W k) (W (k + 1)) (coinAt σ k)
    (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
      (alAmt sevm k).toBytes) RawCallOk U 0x760 0x64 0x820 (P.pullDebit k) (P.pullNext k)
  balB : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm (W 2) (W 2) (coinAt σ 2)
    (balanceOfData sevm.currentTarget) B1 U 0x53c 0x24 0x5a0 P.balBDebit P.balBNext
  balA : alAmt sevm 2 ≠ 0 → StaticWordCallProfile sevm (W 3) (W 3) (coinAt σ 2)
    (balanceOfData sevm.currentTarget) B2 U 0x87c 0x24 0x8e0 P.balADebit P.balANext
  mint : MutableCallProfile sevm (W 3) (W 4) (σ.get tokenSlot)
    (mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes) (fun r => 32 ≤ r.length) U 0xc7c 0x44
    0xd00 P.mintDebit P.mintNext

/-! ## The loop's three iteration shapes -/

section Iter

variable (sevm : Sevm) (σ : Stor) (P : ALExactCalls)

/-- A head's charge on the loop's path: the first deposit's first head (`229`), else
`alHeadCost`. -/
def alHeadCostX (n : Devm) (k : Nat) (T : B256) : Nat :=
  if k = 0 ∧ T = 0 then 229 + sloadCost sevm n (coinsBase + Nat.toB256 0) else alHeadCost sevm n k T

/-- The base after a head: `coins[k]` read. -/
abbrev alHB (n : Devm) (k : Nat) : Devm := afterSload sevm n (coinsBase + Nat.toB256 k)

/-! ### A zero amount -/

/-- A skipped iteration's charge: the head, the credit (`184`), the loop test (`10`). -/
def alSkipCost (n : Devm) (k : Nat) (T : B256) : Nat := alHeadCostX sevm n k T + 194

/-- A skipped iteration's memory: the head's and the credit of `old k + 0`. -/
def alSkipMem (m : Mem) (k : Nat) (old : Nat → B256) : Mem :=
  alCreditMem (alHeadMem sevm m σ k) k (old k + alAmt sevm k)

/-! ### A plain coin's pull -/

/-- The plain pull's `transferFrom` successor. -/
def alPlainCall (n : Devm) (m : Mem) (k : Nat) : Devm :=
  P.pullNext k (alPullId2 sevm (alHB sevm n k) [] (alHeadMem sevm m σ k) k) [3, 0x4c0]
    (alPullMemC sevm (alHeadMem sevm m σ k) k)

/-- The plain pull's clamped reply length. -/
def alPlainLen (n : Devm) (m : Mem) (k : Nat) : Nat :=
  min (alPlainCall sevm σ P n m k).returnData.length 32

/-- After a plain pull: the raw tail's canonical base. -/
def alPlainBase (n : Devm) (m : Mem) (k : Nat) : Devm :=
  rawTailBaseNext sevm (alPlainCall sevm σ P n m k) [3, 0x4c0] (alPlainCall sevm σ P n m k).memory
    alPullSite

/-- After a plain pull: the raw tail's memory and the credit of `old k + amount`. -/
def alPlainMem (n : Devm) (m : Mem) (k : Nat) (old : Nat → B256) : Mem :=
  alCreditMem (vyRawMem (alPlainCall sevm σ P n m k).memory 0x800 0x5c0 (alPlainLen sevm σ P n m k)) k
    (old k + alAmt sevm k)

/-- A plain pull's charge: the head, the fee-index test (`28`), the pull's own instructions
(`646` from a memory of `0x520`, `576` from `0x840`), its debit, the raw tail, the join (`30`),
the credit (`184`), the loop test (`10`). -/
def alPlainCost (n : Devm) (m : Mem) (k : Nat) (T : B256) (p : Bool) : Nat :=
  alHeadCostX sevm n k T + 28 + (if p then 576 else 646) +
    P.pullDebit k (alPullId2 sevm (alHB sevm n k) [] (alHeadMem sevm m σ k) k) [3, 0x4c0]
      (alPullMemC sevm (alHeadMem sevm m σ k) k) +
    rawTailCost (alPlainLen sevm σ P n m k) + 30 + 184 + 10

/-! ### The fee coin's pull -/

/-- The fee coin's first `balanceOf(self)` input memory. -/
def alFeeMemB (m : Mem) : Mem := alBalMem sevm (alHeadMem sevm m σ 2) 1312

/-- The fee coin's first `balanceOf(self)` successor. -/
def alFeeCallB (n : Devm) (m : Mem) : Devm := P.balBNext (alHB sevm n 2) [3, 0x4c0] (alFeeMemB sevm σ m)

/-- The memory after the first read, `B1` at `0x4e0`. -/
def alFeeMemP (n : Devm) (m : Mem) (B1 : B256) : Mem :=
  alBalPostMem (alFeeMemB sevm σ m) 1340 1440 (alFeeCallB sevm σ P n m).returnData B1

/-- The fee coin's `transferFrom` successor. -/
def alFeeCallP (n : Devm) (m : Mem) (B1 : B256) : Devm :=
  P.pullNext 2 (alPullId2 sevm (alFeeCallB sevm σ P n m) [] (alFeeMemP sevm σ P n m B1) 2) [3, 0x4c0]
    (alPullMemC sevm (alFeeMemP sevm σ P n m B1) 2)

/-- The fee coin's pull: clamped reply length. -/
def alFeeLen (n : Devm) (m : Mem) (B1 : B256) : Nat :=
  min (alFeeCallP sevm σ P n m B1).returnData.length 32

/-- The raw tail's canonical base after the fee coin's pull. -/
def alFeeBaseR (n : Devm) (m : Mem) (B1 : B256) : Devm :=
  rawTailBaseNext sevm (alFeeCallP sevm σ P n m B1) [3, 0x4c0] (alFeeCallP sevm σ P n m B1).memory
    alPullSite

/-- The raw tail's memory after the fee coin's pull. -/
def alFeeMemR (n : Devm) (m : Mem) (B1 : B256) : Mem :=
  vyRawMem (alFeeCallP sevm σ P n m B1).memory 0x800 0x5c0 (alFeeLen sevm σ P n m B1)

/-- The second `balanceOf(self)` input memory. -/
def alFeeMemA (n : Devm) (m : Mem) (B1 : B256) : Mem := alBalMem sevm (alFeeMemR sevm σ P n m B1) 2144

/-- The second `balanceOf(self)` successor: the iteration's base. -/
def alFeeBase (n : Devm) (m : Mem) (B1 : B256) : Devm :=
  P.balANext (alFeeBaseR sevm σ P n m B1) [3, 0x4c0] (alFeeMemA sevm σ P n m B1)

/-- After the fee coin's pull: the second reply, `B2 - B1` at `0x4e0`, the credit. -/
def alFeeMem (n : Devm) (m : Mem) (B1 B2 : B256) (old : Nat → B256) : Mem :=
  alCreditMem (alBalPostMem (alFeeMemA sevm σ P n m B1) 2172 2272
    (alFeeBase sevm σ P n m B1).returnData (B2 - B1)) 2 (old 2 + (B2 - B1))

/-- The fee coin's iteration charge: the head, the test (`28`), the first read's instructions
(`96` from `0x520`, `90` from `0x840`) and debit, the pull's instructions (`630` / `576`), debit
and raw tail, the second read and the subtraction (`181`) and debit, the credit (`184`), the
loop test (`10`). -/
def alFeeCost (n : Devm) (m : Mem) (B1 : B256) (T : B256) (p : Bool) : Nat :=
  alHeadCostX sevm n 2 T + 28 + (if p then 90 else 96) +
    P.balBDebit (alHB sevm n 2) [3, 0x4c0] (alFeeMemB sevm σ m) + (if p then 576 else 630) +
    P.pullDebit 2 (alPullId2 sevm (alFeeCallB sevm σ P n m) [] (alFeeMemP sevm σ P n m B1) 2) [3, 0x4c0]
      (alPullMemC sevm (alFeeMemP sevm σ P n m B1) 2) +
    rawTailCost (alFeeLen sevm σ P n m B1) + 181 +
    P.balADebit (alFeeBaseR sevm σ P n m B1) [3, 0x4c0] (alFeeMemA sevm σ P n m B1) + 184 + 10

/-! ### One iteration by its amount -/

/-- Iteration `k`'s canonical base. -/
def alItBase (n : Devm) (m : Mem) (k : Nat) (B1 : B256) : Devm :=
  if alAmt sevm k = 0 then alHB sevm n k
  else if k = 2 then alFeeBase sevm σ P n m B1 else alPlainBase sevm σ P n m k

/-- Iteration `k`'s canonical memory. -/
def alItMem (n : Devm) (m : Mem) (k : Nat) (B1 B2 : B256) (old : Nat → B256) : Mem :=
  if alAmt sevm k = 0 then alSkipMem sevm σ m k old
  else if k = 2 then alFeeMem sevm σ P n m B1 B2 old else alPlainMem sevm σ P n m k old

/-- Iteration `k`'s charge. -/
def alItCost (n : Devm) (m : Mem) (k : Nat) (B1 T : B256) (p : Bool) : Nat :=
  if alAmt sevm k = 0 then alSkipCost sevm n k T
  else if k = 2 then alFeeCost sevm σ P n m B1 T p else alPlainCost sevm σ P n m k T p

end Iter

end Blanc.Lift.Curve3Pool
