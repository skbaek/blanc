import Blanc.Lift.Curve3Pool.Walk.RliLiveFrame
import Blanc.Lift.Curve3Pool.Walk.RliLiveWords
import Blanc.Lift.Curve3Pool.ExchangeExactSchedule

/-!
# `remove_liquidity_imbalance`, exact: the calls' data and the canonical schedule

`RLIExactCalls` is data only: the debit and canonical successor of each external call
(3Crv's `totalSupply()`, its `burnFrom`, coin `k`'s `transfer`). `RLIExactPremises` says each
pair is an exact profile at its call window and world step; a coin's `transfer` is required only
where its amount is nonzero, as the call is made only there. `RliWords` are the model's words the
walk reads (`_A`, the three `get_D_mem` inputs and results, the fee iterations' words); the
exact walk and its endpoint pin them by the model's own checks.

The schedule threads a canonical base and a literal memory through the frame exactly as the
stage cores report them (`rx_rli_preE`, `rx_rli_d0E`, `rx_rli_d1E`, `rx_rli_fee*E`, `rx_rli_d2E`,
`rx_rli_push*E`, `rx_rli_end*E`): storage by `afterSload`/`afterSstore`, `_A` by `aBase`, the
identity copies by `identityCallNext`, the raw tails by `rawTailBaseNext`, the external calls by
their profile's `next`. `rliExactCost` is the stage sum; every summand is read at a canonical
state, none is a bound, none observes a run. A zero amount costs `114` and requests no profile.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The calls' functions, as data: debit and canonical successor of the `totalSupply()` read,
the `burnFrom`, and coin `k`'s `transfer`. -/
structure RLIExactCalls where
  supplyDebit : Devm → List B256 → Mem → Nat
  supplyNext : Devm → List B256 → Mem → Devm
  burnDebit : Devm → List B256 → Mem → Nat
  burnNext : Devm → List B256 → Mem → Devm
  pushDebit : Nat → Devm → List B256 → Mem → Nat
  pushNext : Nat → Devm → List B256 → Mem → Devm

/-- **The exact premises**: each call an exact profile with the data's functions, at its window
and along the world chain `W 0 → … → W 4`, at the entry storage `σ`: the supply read in `W 0`,
the burn of `burn` from `W 0` to `W 1`, coin `k`'s nonzero transfer from `W (k + 1)` to
`W (k + 2)`. -/
structure RLIExactPremises (sevm : Sevm) (σ : Stor) (T burn : B256) (W : Nat → Devm → Prop)
    (U : Nat) (P : RLIExactCalls) : Prop where
  supply : StaticWordCallProfile sevm (W 0) (W 0) (σ.get tokenSlot) totalSupplyData T U 0x17c 4
    0x1c0 P.supplyDebit P.supplyNext
  burn : MutableCallProfile sevm (W 0) (W 1) (σ.get tokenSlot)
    (burnFromSel ++ sevm.caller.toB256.toBytes ++ burn.toBytes) (fun r => 32 ≤ r.length) U 0x85c
    0x44 0x8e0 P.burnDebit P.burnNext
  push : ∀ k, k < 3 → rliAmt sevm k ≠ 0 → MutableCallProfile sevm (W (k + 1)) (W (k + 2))
    (σ.get (coinsBase + Nat.toB256 k)) (transferSel ++ sevm.caller.toB256.toBytes ++
      (rliAmt sevm k).toBytes) RawCallOk U 0xaa0 0x44 0xb40 (P.pushDebit k) (P.pushNext k)

/-- The model's words the walk reads: `_A`'s amplification, the three `get_D_mem` inputs and
results, and each fee iteration's fee, stored balance and adjusted balance. -/
structure RliWords where
  amp : Nat
  v0 : Nat
  v1 : Nat
  v2 : Nat
  xa : V3
  xb : V3
  xc : V3
  f0 : B256
  f1 : B256
  f2 : B256
  s0 : B256
  s1 : B256
  s2 : B256
  x0 : B256
  x1 : B256
  x2 : B256

/-! ## Congruences: a stage's data at an actual base equal to the canonical one modulo gas -/

theorem aMemNext_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') (M : Mem)
    (ret w : B256) : aMemNext sevm b M ret w = aMemNext sevm b' M ret w := by
  unfold aMemNext
  rw [Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := futureATimeSlot) h,
    Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := futureASlot) h,
    Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := initialASlot) h,
    Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := initialATimeSlot) h]

theorem rliPreBaseA_congr (sevm : Sevm) {d d' : Devm} (h : Devm.EqModGas d d') :
    Devm.EqModGas (rliPreBaseA sevm d) (rliPreBaseA sevm d') :=
  (h.afterSload sevm _).afterSload sevm _

theorem rliPreBase2_congr (sevm : Sevm) {d d' : Devm} (h : Devm.EqModGas d d') :
    Devm.EqModGas (rliPreBase2 sevm d) (rliPreBase2 sevm d') :=
  (((aBase_congr sevm (rliPreBaseA_congr sevm h)).afterSload sevm _).afterSload sevm _).afterSload
    sevm _

theorem rliPreCost2_congr (sevm : Sevm) {d d' : Devm} (h : Devm.EqModGas d d') :
    rliPreCost2 sevm d = rliPreCost2 sevm d' := by
  have hA := rliPreBaseA_congr sevm h
  have hB := aBase_congr sevm hA
  unfold rliPreCost2
  rw [h.sloadCost_congr, (h.afterSload sevm _).sloadCost_congr, aGas_congr sevm hA,
    hB.sloadCost_congr, (hB.afterSload sevm _).sloadCost_congr,
    ((hB.afterSload sevm _).afterSload sevm _).sloadCost_congr]

theorem rliPreMem2_congr (sevm : Sevm) {d d' : Devm} (h : Devm.EqModGas d d') (Ms : Mem) (T : B256)
    (σ : Stor) (amp : Nat) : rliPreMem2 sevm d Ms T σ amp = rliPreMem2 sevm d' Ms T σ amp := by
  unfold rliPreMem2
  rw [h.returnData]
  simp only [aMemNext_congr sevm (rliPreBaseA_congr sevm h)]

theorem rliPushId2_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') (S : List B256)
    (M : Mem) (k : Nat) : Devm.EqModGas (rliPushId2 sevm b S M k) (rliPushId2 sevm b' S M k) :=
  identityCallNext_congr sevm _ _ _ _ _ _ (identityCallNext_congr sevm _ _ _ _ _ _ h)

/-- `D1`'s memory sees only the bytes of its input: its first growing store (`amp` at `0x520`)
makes two inputs equal at every byte literally equal. -/
theorem rliD1Mem_congr (sevm : Sevm) {M N : Mem} (h : Mem.EqExcept M N fun _ => False)
    (hs : M.size = 0x520) (n0 n1 n2 A : B256) (x : V3) (v : Nat) :
    rliD1Mem sevm M n0 n1 n2 A x v = rliD1Mem sevm N n0 n1 n2 A x v := by
  have hw : memWord M = memWord N := funext (eqB_memWord h)
  have hsv : (saveMem M 0x4a0 (0x140 + 32 * 0) (26 + 1)).size = 0x520 := by
    rw [saveMem_size (by rw [hs]; decide), hs]
  have h4 := eqB_write (eqB_write (eqB_write (eqB_saveMem h 0x4a0 (0x140 + 32 * 0) (26 + 1)) 0x4c0
    n0.toBytes) 0x4e0 n1.toBytes) 0x500 n2.toBytes
  have e1 : ((saveMem M 0x4a0 (0x140 + 32 * 0) (26 + 1)).write 0x4c0 n0.toBytes).size = 0x520 := by
    rw [Mem.size_write_word_of_add_le (by rw [hsv]; decide), hsv]
  have e2 : (((saveMem M 0x4a0 (0x140 + 32 * 0) (26 + 1)).write 0x4c0 n0.toBytes).write 0x4e0
      n1.toBytes).size = 0x520 := by
    rw [Mem.size_write_word_of_add_le (by rw [e1]; decide), e1]
  have hs4 : ((((saveMem M 0x4a0 (0x140 + 32 * 0) (26 + 1)).write 0x4c0 n0.toBytes).write 0x4e0
      n1.toBytes).write 0x500 n2.toBytes).size = 0x520 := by
    rw [Mem.size_write_word_of_add_le (by rw [e2]), e2]
  have h5 := eqB_write_word_grow (o := 0x520) h4 A (by rw [hs4]; decide)
  simp only [rliD1Mem, h5, hw]

/-! ## The canonical schedule -/

section Schedule

variable (sevm : Sevm) (pre : Devm) (P : RLIExactCalls) (T : B256) (w : RliWords)

/-- The entry storage. -/
abbrev rliσ : Stor := pre.getStor sevm.currentTarget

/-- The memory the dispatcher leaves. -/
abbrev rliMv : Mem := vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- The `totalSupply()` call's canonical successor. -/
def rliSupNext : Devm := P.supplyNext (rliSupBase sevm pre) [] (rliSupMem (rliMv sevm))

/-- The canonical base and memory at the first frame save. -/
def rliN1 : Devm := rliPreBase2 sevm (rliSupNext sevm pre P)
def rliM1 : Mem := rliPreMem2 sevm (rliSupNext sevm pre P) (rliSupMem (rliMv sevm)) T
  (rliσ sevm pre) w.amp

/-- `new_balances[k]`. -/
abbrev rliNew (k : Nat) : B256 := balAt (rliσ sevm pre) k - rliAmt sevm k

/-- The canonical memory after `D0` (up to bytes) and after `D1` (literal). -/
def rliM2 : Mem := rliD0Mem sevm (rliM1 sevm pre P T w) (balAt (rliσ sevm pre) 0)
  (balAt (rliσ sevm pre) 1) (balAt (rliσ sevm pre) 2) (Nat.toB256 w.amp) w.xa w.v0
def rliM3 : Mem := rliD1Mem sevm (rliM2 sevm pre P T w) (rliNew sevm pre 0) (rliNew sevm pre 1)
  (rliNew sevm pre 2) (Nat.toB256 w.amp) w.xb w.v1

/-- The fee loop: the bases after each balance store, the literal memories. -/
def rliNF1 : Devm := afterSstore sevm (rliN1 sevm pre P) (balancesBase + Nat.toB256 0) w.s0
def rliNF2 : Devm := afterSstore sevm (rliNF1 sevm pre P w) (balancesBase + Nat.toB256 1) w.s1
def rliNF3 : Devm := afterSstore sevm (rliNF2 sevm pre P w) (balancesBase + Nat.toB256 2) w.s2
def rliMF1 : Mem := rliFeeMem (rliM3 sevm pre P T w) 0 (Nat.toB256 w.v0) (Nat.toB256 w.v1)
  (balAt (rliσ sevm pre) 0) (rliNew sevm pre 0) w.f0 w.x0
def rliMF2 : Mem := rliFeeMem (rliMF1 sevm pre P T w) 1 (Nat.toB256 w.v0) (Nat.toB256 w.v1)
  (balAt (rliσ sevm pre) 1) (rliNew sevm pre 1) w.f1 w.x1
def rliMF3 : Mem := rliFeeMem (rliMF2 sevm pre P T w) 2 (Nat.toB256 w.v0) (Nat.toB256 w.v1)
  (balAt (rliσ sevm pre) 2) (rliNew sevm pre 2) w.f2 w.x2

/-- The fee loop's charge: each iteration's fixed charge and its balance store at the actual
base. -/
def rliFeeLoopCost : Nat :=
  rliFeeCost 868 (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 0) (rliNew sevm pre 0) +
    sstoreCost sevm (rliN1 sevm pre P) (balancesBase + Nat.toB256 0) w.s0 +
  rliFeeCost 861 (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 1) (rliNew sevm pre 1) +
    sstoreCost sevm (rliNF1 sevm pre P w) (balancesBase + Nat.toB256 1) w.s1 +
  rliFeeCost 861 (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 2) (rliNew sevm pre 2) +
    sstoreCost sevm (rliNF2 sevm pre P w) (balancesBase + Nat.toB256 2) w.s2

/-- The burn's base, memory and canonical successor. -/
def rliBurnBase : Devm := afterSload sevm (rliNF3 sevm pre P w) (Bytes.toB256 [5])
def rliBurnMemC : Mem := rliBurnMem sevm (rliMF3 sevm pre P T w) w.x0 w.x1 w.x2 (Nat.toB256 w.amp)
  w.xc w.v2 (Nat.toB256 w.v0) T
def rliBurnPost : Devm := P.burnNext (rliBurnBase sevm pre P w) [] (rliBurnMemC sevm pre P T w)

/-- `D2`, the burn and its reply check. -/
def rliBurnCost : Nat :=
  6358 + costGetDMem w.xc w.amp + sloadCost sevm (rliNF3 sevm pre P w) (Bytes.toB256 [5]) + 2 +
    P.burnDebit (rliBurnBase sevm pre P w) [] (rliBurnMemC sevm pre P T w) + 70

end Schedule

/-! ## The transfer loop -/

section Push

variable (sevm : Sevm) (P : RLIExactCalls)

/-- The transfer loop's stack below its loop words. -/
abbrev rliPushStk : List B256 := [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [9, 0]]

/-- Coin `k`'s `transfer` base: `coins[k]` read after the payload's identity copies. -/
def rliPushCallBase (n : Devm) (m : Mem) (k : Nat) : Devm :=
  afterSload sevm (rliPushId2 sevm n [] m k) (coinsBase + Nat.toB256 k)

/-- Coin `k`'s `transfer` canonical successor. -/
def rliPushPost (n : Devm) (m : Mem) (k : Nat) : Devm :=
  P.pushNext k (rliPushCallBase sevm n m k) rliPushStk (rliPushMemC sevm m k)

/-- Iteration `k`'s charge: a zero amount `114`; a transfer its fixed charge (`732` from a memory
of `0x920`, `682` after an earlier transfer), `coins[k]`, `GAS`, the debit, the raw tail and
`46`. -/
def rliPushCost (n : Devm) (m : Mem) (k : Nat) (seen : Bool) : Nat :=
  if rliAmt sevm k = 0 then 114 else
    (if seen then 682 else 732) +
      sloadCost sevm (rliPushId2 sevm n [] m k) (coinsBase + Nat.toB256 k) + 2 +
      P.pushDebit k (rliPushCallBase sevm n m k) rliPushStk (rliPushMemC sevm m k) + 46 +
      rawTailCost (min (rliPushPost sevm P n m k).returnData.length 32)

/-- Iteration `k`'s canonical base. -/
def rliPushBase (n : Devm) (m : Mem) (k : Nat) : Devm :=
  if rliAmt sevm k = 0 then n else
    rawTailBaseNext sevm (rliPushPost sevm P n m k) rliPushStk (rliPushPost sevm P n m k).memory
      rliPushSite

/-- Iteration `k`'s literal memory. -/
def rliPushMemNext (n : Devm) (m : Mem) (k : Nat) : Mem :=
  if rliAmt sevm k = 0 then m.write 0x900 (Bytes.toB256 [1] + Nat.toB256 k).toBytes else
    (vyRawMem (rliPushPost sevm P n m k).memory 0xb20 0x920
      (min (rliPushPost sevm P n m k).returnData.length 32)).write 0x900
      (Bytes.toB256 [1] + Nat.toB256 k).toBytes

end Push

section Total

variable (sevm : Sevm) (pre : Devm) (P : RLIExactCalls) (T : B256) (w : RliWords)

/-- The transfer loop's entry: the burn's successor, the counter zeroed at `0x900`. -/
def rliP0 : Devm := rliBurnPost sevm pre P T w
def rliPM0 : Mem := (rliBurnPost sevm pre P T w).memory.write 0x900 (Bytes.toB256 [0]).toBytes

/-- The event and the lock's reset at its actual price from base `n`: `3432` over the memory of
`0x920` (no transfer made), `3372` over `0xb60`. -/
def rliEndCostAt (n : Devm) (grown : Bool) : Nat :=
  (if grown then 3372 else 3432) +
    sstoreCost sevm n (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])

/-- From iteration 2 to `STOP`, at base `n`, memory `m`, `seen` an earlier transfer. -/
def rliTail2Cost (n : Devm) (m : Mem) (seen : Bool) : Nat :=
  rliPushCost sevm P n m 2 seen +
    rliEndCostAt sevm (rliPushBase sevm P n m 2) (seen || !decide (rliAmt sevm 2 = 0))

/-- From iteration 1 to `STOP`. -/
def rliTail1Cost (n : Devm) (m : Mem) (seen : Bool) : Nat :=
  rliPushCost sevm P n m 1 seen +
    rliTail2Cost sevm P (rliPushBase sevm P n m 1) (rliPushMemNext sevm P n m 1)
      (seen || !decide (rliAmt sevm 1 = 0))

/-- The transfer loop, the event and the lock's reset. -/
def rliTail0Cost (n : Devm) (m : Mem) : Nat :=
  rliPushCost sevm P n m 0 false +
    rliTail1Cost sevm P (rliPushBase sevm P n m 0) (rliPushMemNext sevm P n m 0)
      (!decide (rliAmt sevm 0 = 0))

/-- **`remove_liquidity_imbalance`'s exact cost**: the dispatcher (`480`), the prologue with the
supply debit, `D0` (`3117 + costGetDMem`), `D1` (`3898 + costGetDMem`), the fee loop, `D2` and
the burn, the transfers, the event and the lock's reset; each at its canonical state, with the
calls' data `P` and the model's words `w`. -/
def rliExactCost : Nat :=
  480 + rliPreCost1 sevm pre + P.supplyDebit (rliSupBase sevm pre) [] (rliSupMem (rliMv sevm)) +
    rliPreCost2 sevm (rliSupNext sevm pre P) + (3117 + costGetDMem w.xa w.amp) +
    (3898 + costGetDMem w.xb w.amp) + rliFeeLoopCost sevm pre P w + rliBurnCost sevm pre P T w +
    rliTail0Cost sevm P (rliP0 sevm pre P T w) (rliPM0 sevm pre P T w)

end Total

end Blanc.Lift.Curve3Pool
