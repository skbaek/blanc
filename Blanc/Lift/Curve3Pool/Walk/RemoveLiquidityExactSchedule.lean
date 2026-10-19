import Blanc.Lift.Curve3Pool.ExactLivePremises
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLive
import Blanc.Lift.StaticGasTransport

/-!
# `remove_liquidity`, exact: the canonical schedule and its finite cost

`RLExactCalls` is data only: the five calls' debit and canonical-successor functions (the
`totalSupply` read, the three coin transfers, the `burnFrom`). `RLExactPremises` says each pair
is an exact profile (`StaticWordCallProfile` / `MutableCallProfile`) at the call's own window and
world step. Both are fixed before any residual gas.

The schedule threads a canonical base and an explicit memory through the frame, exactly as the
walk's stage cores (`rx_rl_preE`, `rx_rl_s1AL`/`rx_rl_s1BL`, `rx_rl_s2AL`/`rx_rl_s2BL`,
`rx_rl_s3E`, `rx_rl_postE`) report them: storage carriers by `afterSload`/`afterSstore`, the
identity copies by `identityCallNext`/`rawTailBaseNext`, the external calls by their profile's
`next`, every memory as its literal `Mem` term. `rlExactCost` is the stage sum: the
dispatcher's 451, the prologue's `rlPreCost`, the supply debit and its 135, three iterations
(`rlIterCost`), and the burn, event and lock reset (`rlPostExactCost`). Every summand is read at
a canonical state; none is a bound and none observes a run.

The stage costs are stable modulo gas in their bases (`rlS1CostA_congr`, …), which is how the
walk's actual states, equal to the canonical ones modulo gas, are priced by this sum.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The five exact calls' functions, as data: debit and canonical successor of the
`totalSupply` read, of coin `i`'s `transfer`, and of the `burnFrom`. -/
structure RLExactCalls where
  supplyDebit : Devm → List B256 → Mem → Nat
  supplyNext : Devm → List B256 → Mem → Devm
  pushDebit : Nat → Devm → List B256 → Mem → Nat
  pushNext : Nat → Devm → List B256 → Mem → Devm
  burnDebit : Devm → List B256 → Mem → Nat
  burnNext : Devm → List B256 → Mem → Devm

/-- The exact relation a profile gives one call: the input gas is the post's plus the debit, and
the post is the canonical successor modulo gas. -/
def ExactE (debit : Devm → List B256 → Mem → Nat) (next : Devm → List B256 → Mem → Devm) :
    Devm → List B256 → Mem → Nat → Devm → Prop :=
  fun b S M G d => G = d.gasLeft + debit b S M ∧ Devm.EqModGas d (next b S M)

/-- **The exact premises**: each of the five calls is an exact profile with the data's
functions, at its window and along the world chain `W 0 → W 1 → W 2 → W 3 → W 4`. -/
def RLExactPremises (sevm : Sevm) (pre : Devm) (T : B256) (W : Nat → Devm → Prop) (U : Nat)
    (P : RLExactCalls) : Prop :=
  StaticWordCallProfile sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot)
      totalSupplyData T U 0x17c 4 0x1c0 P.supplyDebit P.supplyNext ∧
    (∀ i, i < 3 → MutableCallProfile sevm (W i) (W (i + 1))
      (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++
        (balAt (pre.getStor sevm.currentTarget) i * rlAmt sevm / T).toBytes)
      RawCallOk U 0x520 0x44 0x5c0 (P.pushDebit i) (P.pushNext i)) ∧
    MutableCallProfile sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (burnFromSel ++ sevm.caller.toB256.toBytes ++ (rlAmt sevm).toBytes)
      (fun r => 32 ≤ r.length) U 0x61c 0x44 0x6a0 P.burnDebit P.burnNext

/-! ## Profiles as relation premises -/

/-- A static-word profile answers the relation premise with its exact relation. -/
theorem StaticWordCallProfile.okE {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {A : B256} {U : Nat} {ii is oi : B256} {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (hp : StaticWordCallProfile sevm W W' t data A U ii is oi debit next) :
    StaticWordOkAtE sevm W W' t data A U ii is oi (ExactE debit next) := by
  intro b S M G hW hU hG hin hS
  obtain ⟨hc, d, hrun, hgas, hnext, out, hpost, hlen, hlt, hA, hW', hid⟩ :=
    hp.sound b S M G ⟨hW, hU, hG, hin, hS⟩
  exact ⟨d, out, hrun, hpost, hlen, hlt, hA, by omega, by omega, hW', hid, hgas, hnext⟩

/-- A mutable profile answers the relation premise with its exact relation. -/
theorem MutableCallProfile.okE {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {ok : Bytes → Prop} {U : Nat} {ii is oi : B256} {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (hp : MutableCallProfile sevm W W' t data ok U ii is oi debit next) :
    MutCallOkAtE sevm W W' t data ok U ii is oi (ExactE debit next) := by
  intro b S M G hW hU hG hin hS
  obtain ⟨hc, d, hrun, hgas, hnext, hpost, hok, hlt, hstor, hW', hid⟩ :=
    hp.sound b S M G ⟨hW, hU, hG, hin, hS⟩
  exact ⟨d, hrun, hpost, hok, hlt, by omega, by omega, hstor, hW', hid, hgas, hnext⟩

/-- The burn's mutable profile answers `BurnOkToE` with its exact relation. -/
theorem MutableCallProfile.burnOkToE {sevm : Sevm} {W W' : Devm → Prop} {t amt : B256} {U : Nat}
    {debit : Devm → List B256 → Mem → Nat} {next : Devm → List B256 → Mem → Devm}
    (hp : MutableCallProfile sevm W W' t (burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes)
      (fun r => 32 ≤ r.length) U 0x61c 0x44 0x6a0 debit next) :
    BurnOkToE sevm W W' t amt U (ExactE debit next) := by
  intro b S M G hW hU hG hin hS
  obtain ⟨d, hrun, hpost, hok, hlt, h1, h2, hstor, hW', -, hE⟩ :=
    MutableCallProfile.okE hp b S M G hW hU hG hin hS
  exact ⟨d, hrun, hpost, hok, hlt, h1, h2, hstor, hW', hE⟩

/-! ## Stage costs are stable modulo gas -/

theorem rlPreCost_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') :
    rlPreCost sevm b = rlPreCost sevm b' := by
  unfold rlPreCost
  rw [h.sloadCost_congr, (h.afterSload sevm _).sstoreCost_congr,
    ((h.afterSload sevm _).afterSstore sevm _ _).sloadCost_congr]

theorem rlS1CostA_congr (sevm : Sevm) {b b' : Devm} (i : Nat) (B T : B256)
    (h : Devm.EqModGas b b') : rlS1CostA sevm b i B T = rlS1CostA sevm b' i B T := by
  unfold rlS1CostA
  rw [h.sloadCost_congr, (h.afterSload sevm _).sloadCost_congr,
    ((h.afterSload sevm _).afterSload sevm _).sstoreCost_congr]

theorem rlS1CostB_congr (sevm : Sevm) {b b' : Devm} (i : Nat) (B T : B256)
    (h : Devm.EqModGas b b') : rlS1CostB sevm b i B T = rlS1CostB sevm b' i B T := by
  unfold rlS1CostB
  rw [h.sloadCost_congr, (h.afterSload sevm _).sloadCost_congr,
    ((h.afterSload sevm _).afterSload sevm _).sstoreCost_congr]

theorem rlS3Cost_congr (sevm : Sevm) {b b' : Devm} (i : Nat) (h : Devm.EqModGas b b') :
    rlS3Cost sevm b i = rlS3Cost sevm b' i := by
  unfold rlS3Cost
  rw [h.sloadCost_congr]

theorem rlPostCost_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') :
    rlPostCost sevm b = rlPostCost sevm b' := by
  unfold rlPostCost
  rw [h.sloadCost_congr]

/-! ## The canonical schedule -/

section Schedule

variable (sevm : Sevm) (pre : Devm) (T : B256) (P : RLExactCalls)

/-- `balances[i]` at the frame's entry. -/
abbrev rlB (i : Nat) : B256 := balAt (pre.getStor sevm.currentTarget) i

/-- The amount coin `i` pays out, at the entry balances and supply `T`. -/
abbrev rlV (i : Nat) : B256 := rlB sevm pre i * rlAmt sevm / T

/-- The `balances` key of coin `i`. -/
abbrev rlKey (i : Nat) : B256 := balancesBase + Nat.toB256 i

/-- The canonical base after the loop body's storage step (two reads and the debit write). -/
def rlS1Base (i : Nat) (n : Devm) : Devm :=
  afterSstore sevm (afterSload sevm (afterSload sevm n (rlKey i)) (rlKey i)) (rlKey i)
    (rlB sevm pre i - rlB sevm pre i * rlAmt sevm / T)

/-- The canonical base after the payload's two identity copies. -/
def rlS2Base (i : Nat) (n : Devm) (m : Mem) : Devm :=
  rlS2Next sevm (rlS1Base sevm pre T i n) (rlS1Mem m (rlV sevm pre T i)) i (rlV sevm pre T i)

/-- The payload's memory after both identity copies. -/
def rlS2MemOf (i : Nat) (m : Mem) : Mem :=
  rlS2Mem sevm (rlS1Mem m (rlV sevm pre T i)) i (rlV sevm pre T i)

/-- The `transfer` call's base: `coins[i]` read. -/
def rlPushBase (i : Nat) (n : Devm) (m : Mem) : Devm :=
  afterSload sevm (rlS2Base sevm pre T i n m) (coinsBase + Nat.toB256 i)

/-- The `transfer` call's memory: the key word cleared at `0xc0`. -/
def rlPushMem (i : Nat) (m : Mem) : Mem :=
  (rlS2MemOf sevm pre T i m).write 0xc0 (Bytes.toB256 [0]).toBytes

/-- The `transfer` call's canonical successor. -/
def rlPushNext (i : Nat) (n : Devm) (m : Mem) : Devm :=
  P.pushNext i (rlPushBase sevm pre T i n m) [3, 0x2a0] (rlPushMem sevm pre T i m)

/-- The `transfer` call's debit. -/
def rlPushDebit (i : Nat) (n : Devm) (m : Mem) : Nat :=
  P.pushDebit i (rlPushBase sevm pre T i n m) [3, 0x2a0] (rlPushMem sevm pre T i m)

/-- The reply's clamped length. -/
def rlReplyLen (i : Nat) (n : Devm) (m : Mem) : Nat :=
  min (rlPushNext sevm pre T P i n m).returnData.length 32

/-- The next loop head's canonical base: the raw-call tail's identity copy. -/
def rlIterBase (i : Nat) (n : Devm) (m : Mem) : Devm :=
  rawTailBaseNext sevm (rlPushNext sevm pre T P i n m) [3, 0x2a0]
    (rlPushNext sevm pre T P i n m).memory rlSite

/-- The next loop head's memory: the raw-call tail's, with the counter advanced. -/
def rlIterMem (i : Nat) (n : Devm) (m : Mem) : Mem :=
  (vyRawMem (rlPushNext sevm pre T P i n m).memory 0x5a0 0x3a0 (rlReplyLen sevm pre T P i n m)).write
    0x2a0 (Nat.toB256 (i + 1)).toBytes

/-- One iteration's charge after its storage-step price `s1`: the payload's fixed price
included in `s1`, `coins[i]`, the `transfer` debit, the raw tail, the increment. -/
def rlIterCost (i : Nat) (n : Devm) (m : Mem) (s1 : Nat) : Nat :=
  s1 + rlS3Cost sevm (rlS2Base sevm pre T i n m) i + rlPushDebit sevm pre T P i n m +
    rawTailCost (rlReplyLen sevm pre T P i n m) + 45

/-- The `totalSupply` call's base and memory. -/
abbrev rlSupBase : Devm := rlSupplyBase sevm pre

/-- The first loop head's canonical base: the supply call's successor. -/
def rlHead0 : Devm := P.supplyNext (rlSupplyBase sevm pre) [] (rlSupplyMem sevm)

/-- The first loop head's memory. -/
def rlHeadMem0 : Mem := rlLoopMem0 sevm T (rlHead0 sevm pre P).memory

/-- The second loop head. -/
def rlHead1 : Devm := rlIterBase sevm pre T P 0 (rlHead0 sevm pre P) (rlHeadMem0 sevm pre T P)
def rlHeadMem1 : Mem := rlIterMem sevm pre T P 0 (rlHead0 sevm pre P) (rlHeadMem0 sevm pre T P)

/-- The third loop head. -/
def rlHead2 : Devm := rlIterBase sevm pre T P 1 (rlHead1 sevm pre T P) (rlHeadMem1 sevm pre T P)
def rlHeadMem2 : Mem := rlIterMem sevm pre T P 1 (rlHead1 sevm pre T P) (rlHeadMem1 sevm pre T P)

/-- The loop exit. -/
def rlHead3 : Devm := rlIterBase sevm pre T P 2 (rlHead2 sevm pre T P) (rlHeadMem2 sevm pre T P)
def rlHeadMem3 : Mem := rlIterMem sevm pre T P 2 (rlHead2 sevm pre T P) (rlHeadMem2 sevm pre T P)

/-- The three iterations' charges. -/
def rlIter0Cost : Nat :=
  rlIterCost sevm pre T P 0 (rlHead0 sevm pre P) (rlHeadMem0 sevm pre T P)
    (rlS1CostA sevm (rlHead0 sevm pre P) 0 (rlB sevm pre 0) T + 532)
def rlIter1Cost : Nat :=
  rlIterCost sevm pre T P 1 (rlHead1 sevm pre T P) (rlHeadMem1 sevm pre T P)
    (rlS1CostB sevm (rlHead1 sevm pre T P) 1 (rlB sevm pre 1) T + 482)
def rlIter2Cost : Nat :=
  rlIterCost sevm pre T P 2 (rlHead2 sevm pre T P) (rlHeadMem2 sevm pre T P)
    (rlS1CostB sevm (rlHead2 sevm pre T P) 2 (rlB sevm pre 2) T + 482)

/-- The `burnFrom` call's base: the token slot read at the loop exit. -/
def rlBurnBase : Devm := afterSload sevm (rlHead3 sevm pre T P) tokenSlot

/-- The burn, its reply check, the event, and the lock's reset at its actual price. -/
def rlPostExactCost : Nat :=
  rlPostCost sevm (rlHead3 sevm pre T P) +
    P.burnDebit (rlBurnBase sevm pre T P) [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P)) + 3138 +
    sstoreCost sevm (P.burnNext (rlBurnBase sevm pre T P) [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P)))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])

/-- **`remove_liquidity`'s exact cost**: a finite sum of independently priced stages, each at its
canonical state. It depends on the entry, the supply `T` and the calls' data `P`, never on the
gas the frame is given. -/
def rlExactCost : Nat :=
  451 + rlPreCost sevm pre + P.supplyDebit (rlSupplyBase sevm pre) [] (rlSupplyMem sevm) + 135 +
    rlIter0Cost sevm pre T P + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
    rlPostExactCost sevm pre T P

end Schedule

/-! ## The static initial-gas coordinate

A message entry's static machine records its initial gas. Changing only that field changes
neither the schedule, nor its cost, nor the exact premises with the same data `P`, nor a closed
world invariant: the profiles are transported with their functions unchanged
(`StaticWordCallProfile.withStaticGas`, `MutableCallProfile.withStaticGas`). -/

section StaticGas

variable (sevm : Sevm) (F : Nat)

/-- The exact cost ignores the frame's static initial gas, with the data `P` fixed. -/
theorem rlExactCost_withStaticGas (pre : Devm) (T : B256) (P : RLExactCalls) :
    rlExactCost {sevm with gas := F} pre T P = rlExactCost sevm pre T P := by
  simp only [rlExactCost, rlPreCost, rlSupplyBase, rlSupplyMem, rlIter0Cost, rlIter1Cost,
    rlIter2Cost, rlPostExactCost, rlIterCost, rlPushDebit, rlPushNext, rlPushBase, rlPushMem,
    rlReplyLen, rlS2Base, rlS2MemOf, rlS1Base, rlHead0, rlHead1, rlHead2, rlHead3, rlHeadMem0,
    rlHeadMem1, rlHeadMem2, rlHeadMem3, rlIterBase, rlIterMem, rlBurnBase, rlS1CostA, rlS1CostB,
    rlS3Cost, rlPostCost, rlLoopMem0, rlBurnMem, rlS2Next, rlS2Mem, rlS2Mem2, rlS2Base1, rlV, rlB,
    rlAmt, sloadCost_withStaticGas, sstoreCost_withStaticGas, afterSload_withStaticGas,
    afterSstore_withStaticGas, dataWord_withStaticGas, identityCallNext_withStaticGas,
    rawTailBaseNext_withStaticGas]

end StaticGas

/-- The exact premises survive a change of static initial gas, with the same data `P`. -/
theorem RLExactPremises.withStaticGas {sevm : Sevm} {pre : Devm} {T : B256}
    {W : Nat → Devm → Prop} {U : Nat} {P : RLExactCalls}
    (h : RLExactPremises sevm pre T W U P) (F : Nat) :
    RLExactPremises {sevm with gas := F} pre T W U P := by
  obtain ⟨hs, hp, hb⟩ := h
  exact ⟨hs.withStaticGas F, fun i hi => (hp i hi).withStaticGas F, hb.withStaticGas F⟩

/-- A closed world invariant stays closed when only the static initial gas changes. -/
theorem WClosed.withStaticGas {sevm : Sevm} {W : Devm → Prop} (h : WClosed sevm W) (F : Nat) :
    WClosed {sevm with gas := F} W :=
  ⟨h.st, h.sload, h.sstore, h.sha, h.log⟩

/-! ## The compact regrouping

`rlExactCost` regroups as the fixed `7384` plus twelve ordered `SLOAD` charges and five
`SSTORE` charges at the schedule's actual intermediate worlds, the five call debits and the
three raw-tail charges. -/

section Regroup

variable (sevm : Sevm) (pre : Devm) (T : B256) (P : RLExactCalls)

/-- An iteration's ordered storage charges from its head `n`: the two `balances[i]` reads, the
debit write, and the `coins[i]` read after the payload. -/
def rlIterStorageCost (i : Nat) (n : Devm) (m : Mem) : Nat :=
  sloadCost sevm n (rlKey i) + sloadCost sevm (afterSload sevm n (rlKey i)) (rlKey i) +
    sstoreCost sevm (afterSload sevm (afterSload sevm n (rlKey i)) (rlKey i)) (rlKey i)
      (rlB sevm pre i - rlB sevm pre i * rlAmt sevm / T) +
    sloadCost sevm (rlS2Base sevm pre T i n m) (coinsBase + Nat.toB256 i)

/-- The prologue's and the tail's ordered storage charges: the lock read and set, the token slot
read; the token slot read at the loop exit and the lock's reset after the event. -/
def rlEdgeStorageCost : Nat :=
  sloadCost sevm pre (Bytes.toB256 [0xff, 0xff, 0xff]) +
    sstoreCost sevm (afterSload sevm pre (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm pre (Bytes.toB256 [0xff, 0xff, 0xff]))
      (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) (Bytes.toB256 [5]) +
    sloadCost sevm (rlHead3 sevm pre T P) tokenSlot +
    sstoreCost sevm (P.burnNext (rlBurnBase sevm pre T P) []
      (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])

/-- The five call debits, at the calls' canonical inputs. -/
def rlDebits : Nat :=
  P.supplyDebit (rlSupplyBase sevm pre) [] (rlSupplyMem sevm) +
    rlPushDebit sevm pre T P 0 (rlHead0 sevm pre P) (rlHeadMem0 sevm pre T P) +
    rlPushDebit sevm pre T P 1 (rlHead1 sevm pre T P) (rlHeadMem1 sevm pre T P) +
    rlPushDebit sevm pre T P 2 (rlHead2 sevm pre T P) (rlHeadMem2 sevm pre T P) +
    P.burnDebit (rlBurnBase sevm pre T P) [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P))

/-- The three raw-call tails' charges, at the canonical replies' clamped lengths. -/
def rlRawTails : Nat :=
  rawTailCost (rlReplyLen sevm pre T P 0 (rlHead0 sevm pre P) (rlHeadMem0 sevm pre T P)) +
    rawTailCost (rlReplyLen sevm pre T P 1 (rlHead1 sevm pre T P) (rlHeadMem1 sevm pre T P)) +
    rawTailCost (rlReplyLen sevm pre T P 2 (rlHead2 sevm pre T P) (rlHeadMem2 sevm pre T P))

/-- **The compact cost**: `7384` fixed, twelve ordered `SLOAD` and five `SSTORE` charges, five
debits and three raw tails. -/
theorem rlExactCost_eq : rlExactCost sevm pre T P =
    7384 + rlEdgeStorageCost sevm pre T P +
      rlIterStorageCost sevm pre T 0 (rlHead0 sevm pre P) (rlHeadMem0 sevm pre T P) +
      rlIterStorageCost sevm pre T 1 (rlHead1 sevm pre T P) (rlHeadMem1 sevm pre T P) +
      rlIterStorageCost sevm pre T 2 (rlHead2 sevm pre T P) (rlHeadMem2 sevm pre T P) +
      rlDebits sevm pre T P + rlRawTails sevm pre T P := by
  unfold rlExactCost rlIter0Cost rlIter1Cost rlIter2Cost rlPostExactCost rlIterCost
    rlEdgeStorageCost rlIterStorageCost rlDebits rlRawTails rlPreCost rlS1CostA rlS1CostB
    rlS3Cost rlPostCost rlKey
  omega

end Regroup

end Blanc.Lift.Curve3Pool
