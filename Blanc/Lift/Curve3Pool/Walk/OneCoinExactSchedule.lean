import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveFrame
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityExactSchedule

/-!
# `remove_liquidity_one_coin`, exact: the calls' data and the canonical schedule

`OCExactCalls` is data only: the debit and canonical successor of each of
`remove_liquidity_one_coin`'s three external calls (3Crv's `totalSupply()` inside
`_calc_withdraw_one_coin`, 3Crv's `burnFrom`, coin `i`'s `transfer`). `OCExactPremises` says each
pair is an exact profile at its call window and world step. Both are fixed before any residual
gas.

The schedule follows the stage cores in order: the dispatcher (`578`), the guards
(`ocPreCost`, base `ocPreBase`, memory `ocPreMem`), the internal-call idiom (`19`),
`_calc_withdraw_one_coin` before its `totalSupply()` call (`cwACost`), the call's debit, the rest
of `_calc_withdraw_one_coin` (`cwRestCost`, at the call's canonical successor), the balance store
and the burn (`ocP1Cost`, the burn's debit and the reply test `35`), and the push to `STOP`
(`ocP2Cost`: both payload identity copies, `coins[i]`, the push's debit, its raw tail, the event
and the lock reset). Every base is a canonical successor of `pre`; every memory is the stages'
literal canonical memory; every charge is read there.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The calls' functions, as data: debit and canonical successor of the `totalSupply()` read, the
`burnFrom` and the coin's `transfer`. -/
structure OCExactCalls where
  supplyDebit : Devm → List B256 → Mem → Nat
  supplyNext : Devm → List B256 → Mem → Devm
  burnDebit : Devm → List B256 → Mem → Nat
  burnNext : Devm → List B256 → Mem → Devm
  pushDebit : Devm → List B256 → Mem → Nat
  pushNext : Devm → List B256 → Mem → Devm

/-- **The exact premises**: each of the three calls is an exact profile with the data's functions,
at its window and along the world chain `W → W' → W''` (the supply keeps `W`). `dy` is the pushed
amount. -/
def OCExactPremises (sevm : Sevm) (pre : Devm) (T dy : B256) (W W' W'' : Devm → Prop) (U : Nat)
    (P : OCExactCalls) : Prop :=
  StaticWordCallProfile sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) totalSupplyData
      T U 0x2bc 4 0x300 P.supplyDebit P.supplyNext ∧
    MutableCallProfile sevm W W' ((pre.getStor sevm.currentTarget).get tokenSlot)
      (burnFromSel ++ sevm.caller.toB256.toBytes ++ (ocAmt sevm).toBytes) (fun r => 32 ≤ r.length)
      U 0x31c 0x44 0x3a0 P.burnDebit P.burnNext ∧
    MutableCallProfile sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinsBase + ocI sevm))
      (transferSel ++ sevm.caller.toB256.toBytes ++ dy.toBytes) RawCallOk U 0x540 0x44 0x5e0
      P.pushDebit P.pushNext

/-! ## Stage costs are stable modulo gas -/

theorem xpBase_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') :
    Devm.EqModGas (xpBase sevm b) (xpBase sevm b') :=
  ((h.afterSload sevm _).afterSload sevm _).afterSload sevm _

theorem xpGas_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') :
    xpGas sevm b = xpGas sevm b' := by
  unfold xpGas
  rw [h.sloadCost_congr, (h.afterSload sevm _).sloadCost_congr,
    ((h.afterSload sevm _).afterSload sevm _).sloadCost_congr]

theorem cwRestCost_congr (sevm : Sevm) {d d' : Devm} (h : Devm.EqModGas d d') (amp : Nat)
    (iw x0 x1 x2 D1 r0 r1 r2 : B256) :
    cwRestCost sevm d amp iw x0 x1 x2 D1 r0 r1 r2 = cwRestCost sevm d' amp iw x0 x1 x2 D1 r0 r1 r2 := by
  unfold cwRestCost
  rw [xpGas_congr sevm h]

theorem ocBurnBase_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') (σ : Stor)
    (dy fee : B256) : Devm.EqModGas (ocBurnBase sevm b σ dy fee) (ocBurnBase sevm b' σ dy fee) :=
  (((h.afterSload sevm _).afterSload sevm _).afterSstore sevm _ _).afterSload sevm _

theorem ocP1Cost_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') (σ : Stor)
    (dy fee : B256) : ocP1Cost sevm b σ dy fee = ocP1Cost sevm b' σ dy fee := by
  unfold ocP1Cost
  rw [h.sloadCost_congr, (h.afterSload sevm _).sloadCost_congr,
    ((h.afterSload sevm _).afterSload sevm _).sstoreCost_congr,
    (((h.afterSload sevm _).afterSload sevm _).afterSstore sevm _ _).sloadCost_congr]

/-! ## The canonical schedule -/

section Schedule

variable (sevm : Sevm) (pre : Devm) (P : OCExactCalls) (T : B256) (amp : Nat)
  (x0 x1 x2 D0 y r0 r1 r2 y2 : B256)

/-- The pool's storage after the lock is set. -/
abbrev ocσ1 : Stor :=
  (pre.getStor sevm.currentTarget).set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])

/-- The memory the guards leave, from the dispatcher's. -/
abbrev ocM1 : Mem := ocPreMem sevm (vyMem Mem.empty (Sevm.dataWord sevm 0))

/-- The `totalSupply()` call's base. -/
abbrev ocSupBase : Devm := cwSupBase sevm (aBase sevm (ocPreBase sevm pre))

/-- The `totalSupply()` call's memory. -/
abbrev ocSupMem : Mem :=
  cwAMem sevm (ocPreBase sevm pre) (ocσ1 sevm pre) (ocM1 sevm) (Nat.toB256 (0x448b + 6))
    (ocAmt sevm) (ocI sevm) amp

/-- The `totalSupply()` call's canonical successor. -/
def ocSupNext : Devm :=
  P.supplyNext (ocSupBase sevm pre) [Bytes.toB256 [0], Bytes.toB256 [0]] (ocSupMem sevm pre amp)

/-- The amount pushed. -/
abbrev ocDy : B256 := cwDy (ocI sevm) r0 r1 r2 y2

/-- The fee share retained. -/
abbrev ocFee : B256 :=
  (pickWord3 (ocI sevm).toNat x0 x1 x2 - y) / pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm -
    cwDy (ocI sevm) r0 r1 r2 y2

/-- The memory `_calc_withdraw_one_coin` returns. -/
def ocCwMem : Mem :=
  cwRunMem (cwA2Post (ocSupMem sevm pre amp) (ocSupNext sevm pre P amp).returnData T) x0 x1 x2
    (Nat.toB256 amp) D0 (ocAmt sevm) T (ocI sevm) y r0 r1 r2 y2

/-- The base `_calc_withdraw_one_coin` returns over. -/
abbrev ocCwBase : Devm := xpBase sevm (ocSupNext sevm pre P amp)

/-- The burn's base. -/
abbrev ocBurnIn : Devm :=
  ocBurnBase sevm (ocCwBase sevm pre P amp) (ocσ1 sevm pre) (ocDy sevm r0 r1 r2 y2)
    (ocFee sevm x0 x1 x2 y r0 r1 r2 y2)

/-- The burn's memory. -/
abbrev ocBurnMem : Mem :=
  ocP1Mem sevm (ocCwMem sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2) (ocDy sevm r0 r1 r2 y2)
    (ocFee sevm x0 x1 x2 y r0 r1 r2 y2) (Bytes.toB256 [0]) (Bytes.toB256 [0])

/-- The burn's canonical successor. -/
def ocBurnNext : Devm :=
  P.burnNext (ocBurnIn sevm pre P amp x0 x1 x2 y r0 r1 r2 y2) []
    (ocBurnMem sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2)

end Schedule

section Push

variable (sevm : Sevm) (P : OCExactCalls) (n : Devm) (M : Mem) (dy : B256)

/-- The push payload's first identity successor. -/
def ocPushI1 : Devm :=
  identityCallNext sevm n ocP2S1 (ocP2Mem1 M) (Bytes.toB256 [4, 32] + Bytes.toB256 [32])
    (Bytes.toB256 [4]) (Bytes.toB256 [4, 128] + Bytes.toB256 [0] + Bytes.toB256 [32])
    (Bytes.toB256 [4])

/-- The push payload's second identity successor. -/
def ocPushI2 : Devm :=
  identityCallNext sevm (ocPushI1 sevm n M) ocP2S2 (ocP2Mem2 sevm M dy) (Bytes.toB256 [4, 128])
    (Bytes.toB256 [32] + exPushLen) (Bytes.toB256 [5, 32]) (Bytes.toB256 [32] + exPushLen)

/-- The push call's base: `coins[i]` read at the second identity successor. -/
abbrev ocPushIn : Devm :=
  afterSload sevm (ocPushI2 sevm n M dy) (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36]))

/-- The push call's canonical successor. -/
def ocPushNext : Devm := P.pushNext (ocPushIn sevm n M dy) [] (ocPushMem sevm M dy)

/-- **The exact charge of the push, the event and the lock**: `586` fixed (both payload identity
copies included), `coins[i]`, the push's debit, the raw tail at the reply's actual length, the
`1679` of the event (`LOG2`) and its glue, and the lock reset at the raw tail's canonical
successor. -/
def ocP2Cost : Nat :=
  586 + sloadCost sevm (ocPushI2 sevm n M dy) (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [36])) +
    P.pushDebit (ocPushIn sevm n M dy) [] (ocPushMem sevm M dy) +
    rawTailCost (min (ocPushNext sevm P n M dy).returnData.length 32) + 1679 +
    sstoreCost sevm (rawTailBaseNext sevm (ocPushNext sevm P n M dy) []
      (ocPushNext sevm P n M dy).memory ocPushSite) (Bytes.toB256 [255, 255, 255])
      (Bytes.toB256 [0])

end Push

/-- `_calc_withdraw_one_coin`'s exact charge in the frame: before the `totalSupply()` call
(`cwACost`), the call's debit, and after it (`cwRestCost`, at the call's canonical successor). -/
def ocCwCost (sevm : Sevm) (pre : Devm) (T : B256) (P : OCExactCalls) (amp : Nat)
    (x0 x1 x2 D0 r0 r1 r2 : B256) : Nat :=
  cwACost sevm (ocPreBase sevm pre) +
    P.supplyDebit (ocSupBase sevm pre) [Bytes.toB256 [0], Bytes.toB256 [0]] (ocSupMem sevm pre amp) +
    cwRestCost sevm (ocSupNext sevm pre P amp) amp (ocI sevm) x0 x1 x2 (D0 - ocAmt sevm * D0 / T) r0
      r1 r2

/-- The exact charge after `_calc_withdraw_one_coin`: the balance store, the burn's debit and its
reply test (`35`), then the push to `STOP` (`ocP2Cost`) over the burn's successor. -/
def ocTailCost (sevm : Sevm) (pre : Devm) (T : B256) (P : OCExactCalls) (amp : Nat)
    (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) : Nat :=
  (ocP1Cost sevm (ocCwBase sevm pre P amp) (ocσ1 sevm pre) (ocDy sevm r0 r1 r2 y2)
      (ocFee sevm x0 x1 x2 y r0 r1 r2 y2) +
    P.burnDebit (ocBurnIn sevm pre P amp x0 x1 x2 y r0 r1 r2 y2) []
      (ocBurnMem sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2) + 35) +
  ocP2Cost sevm P (ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2)
    (ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2).memory (ocDy sevm r0 r1 r2 y2)

/-- **`remove_liquidity_one_coin`'s closed exact charge**, at the model's words: the dispatcher
(`578`), the guards (`ocPreCost`), the call idiom (`19`), `_calc_withdraw_one_coin`
(`ocCwCost`), the balance store, the burn and the push to `STOP` (`ocTailCost`). -/
def ocExactCost (sevm : Sevm) (pre : Devm) (T : B256) (P : OCExactCalls) (amp : Nat)
    (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) : Nat :=
  578 + ocPreCost sevm pre + 19 + ocCwCost sevm pre T P amp x0 x1 x2 D0 r0 r1 r2 +
    ocTailCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2



/-! ## The compact regrouping

For a valid coin index, `ocExactCost` regroups as the fixed `24910` plus `_A`'s and `_xp`'s
reads (`aGas`, `xpGas`), the Newton callees' checked costs, the eight ordered `SLOAD` charges and
three `SSTORE` charges outside them at the schedule's actual intermediate worlds, the three call
debits and the push's raw tail. The fee loop charges `546`/`576`, `543`/`573`, `543`/`573` by
whether each coin is `i`; for `i < 3` they sum to `1692` (`cwFeeCost_eq`). -/

theorem ocExactCost_eq {sevm : Sevm} (pre : Devm) (T : B256) (P : OCExactCalls) (amp : Nat)
    (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI sevm).toNat < 3) :
    ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 =
      24910 + aGas sevm (ocPreBase sevm pre) + xpGas sevm (ocSupNext sevm pre P amp) +
      costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp (ocI sevm).toNat x0.toNat x1.toNat x2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      costGetYD amp (ocI sevm).toNat r0.toNat r1.toNat r2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      (ocPreCost sevm pre - 233) +
      (sloadCost sevm (aBase sevm (ocPreBase sevm pre)) (Bytes.toB256 [2]) +
        sloadCost sevm (afterSload sevm (aBase sevm (ocPreBase sevm pre)) (Bytes.toB256 [2]))
          (Bytes.toB256 [5])) +
      P.supplyDebit (ocSupBase sevm pre) [Bytes.toB256 [0], Bytes.toB256 [0]] (ocSupMem sevm pre amp) +
      (ocP1Cost sevm (ocCwBase sevm pre P amp) (ocσ1 sevm pre) (ocDy sevm r0 r1 r2 y2)
        (ocFee sevm x0 x1 x2 y r0 r1 r2 y2) - 494) +
      P.burnDebit (ocBurnIn sevm pre P amp x0 x1 x2 y r0 r1 r2 y2) []
        (ocBurnMem sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2) +
      (ocP2Cost sevm P (ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2)
        (ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2).memory (ocDy sevm r0 r1 r2 y2) -
        2265) := by
  have hf := cwFeeCost_eq hi3
  have he := aE_store sevm (ocPreBase sevm pre)
  have hp0 : 233 ≤ ocPreCost sevm pre := by unfold ocPreCost; omega
  have hp1 : 494 ≤ ocP1Cost sevm (ocCwBase sevm pre P amp) (ocσ1 sevm pre) (ocDy sevm r0 r1 r2 y2)
      (ocFee sevm x0 x1 x2 y r0 r1 r2 y2) := by unfold ocP1Cost; omega
  have hp2 : 2265 ≤ ocP2Cost sevm P (ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2)
      (ocBurnNext sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2).memory (ocDy sevm r0 r1 r2 y2) := by
    unfold ocP2Cost; omega
  unfold ocExactCost ocCwCost cwACost cwA2Cost cwRestCost ocTailCost
  omega

/-! ## The static initial-gas coordinate

A message entry's static machine records its initial gas. Changing only that field changes
neither the schedule nor its cost, nor the exact premises with the same data `P`: the profiles are
transported with their functions unchanged (`StaticWordCallProfile.withStaticGas`,
`MutableCallProfile.withStaticGas`). -/

section StaticGas

variable (sevm : Sevm) (F : Nat)

theorem aBase_withStaticGas (b : Devm) : aBase {sevm with gas := F} b = aBase sevm b := rfl
theorem xpBase_withStaticGas (b : Devm) : xpBase {sevm with gas := F} b = xpBase sevm b := rfl
theorem ocPreBase_withStaticGas (b : Devm) :
    ocPreBase {sevm with gas := F} b = ocPreBase sevm b := rfl
theorem ocPreCost_withStaticGas (b : Devm) :
    ocPreCost {sevm with gas := F} b = ocPreCost sevm b := rfl
theorem ocPreMem_withStaticGas (M : Mem) : ocPreMem {sevm with gas := F} M = ocPreMem sevm M := rfl
theorem cwSupBase_withStaticGas (b : Devm) :
    cwSupBase {sevm with gas := F} b = cwSupBase sevm b := rfl
theorem cwACost_withStaticGas (b : Devm) : cwACost {sevm with gas := F} b = cwACost sevm b := rfl
theorem cwAMem_withStaticGas (b : Devm) (σ : Stor) (M : Mem) (ρ a i : B256) (amp : Nat) :
    cwAMem {sevm with gas := F} b σ M ρ a i amp = cwAMem sevm b σ M ρ a i amp := rfl
theorem cwRestCost_withStaticGas (d : Devm) (amp : Nat) (iw x0 x1 x2 D1 r0 r1 r2 : B256) :
    cwRestCost {sevm with gas := F} d amp iw x0 x1 x2 D1 r0 r1 r2 =
      cwRestCost sevm d amp iw x0 x1 x2 D1 r0 r1 r2 := rfl
theorem ocP1Cost_withStaticGas (b : Devm) (σ : Stor) (dy fee : B256) :
    ocP1Cost {sevm with gas := F} b σ dy fee = ocP1Cost sevm b σ dy fee := rfl
theorem ocBurnBase_withStaticGas (b : Devm) (σ : Stor) (dy fee : B256) :
    ocBurnBase {sevm with gas := F} b σ dy fee = ocBurnBase sevm b σ dy fee := rfl
theorem ocP1Mem_withStaticGas (M : Mem) (dy fee w1 w2 : B256) :
    ocP1Mem {sevm with gas := F} M dy fee w1 w2 = ocP1Mem sevm M dy fee w1 w2 := rfl
theorem ocPushMem_withStaticGas (M : Mem) (dy : B256) :
    ocPushMem {sevm with gas := F} M dy = ocPushMem sevm M dy := rfl
theorem ocPushI2_withStaticGas (n : Devm) (M : Mem) (dy : B256) :
    ocPushI2 {sevm with gas := F} n M dy = ocPushI2 sevm n M dy := rfl

/-- The exact cost ignores the frame's static initial gas, with the data `P` fixed. -/
theorem ocExactCost_withStaticGas (pre : Devm) (T : B256) (P : OCExactCalls)
    (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) :
    ocExactCost {sevm with gas := F} pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 =
      ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 := by
  simp only [ocExactCost, ocCwCost, ocTailCost, ocSupNext, ocCwMem, ocBurnNext, ocP2Cost,
    ocPushNext, ocSupBase, ocSupMem, ocM1, ocσ1, ocCwBase, ocDy, ocFee, ocBurnIn, ocBurnMem,
    ocPushIn, ocAmt, ocI, dataWord_withStaticGas, sloadCost_withStaticGas,
    sstoreCost_withStaticGas, afterSload_withStaticGas, rawTailBaseNext_withStaticGas,
    aBase_withStaticGas, ocPreBase_withStaticGas, ocPreCost_withStaticGas,
    ocPreMem_withStaticGas, cwSupBase_withStaticGas, cwACost_withStaticGas,
    cwAMem_withStaticGas, cwRestCost_withStaticGas, ocP1Cost_withStaticGas,
    ocBurnBase_withStaticGas, ocP1Mem_withStaticGas, ocPushMem_withStaticGas,
    ocPushI2_withStaticGas, xpBase_withStaticGas]

end StaticGas

/-- The exact premises survive a change of static initial gas, with the same data `P`. -/
theorem OCExactPremises.withStaticGas {sevm : Sevm} {pre : Devm} {T dy : B256}
    {W W' W'' : Devm → Prop} {U : Nat} {P : OCExactCalls}
    (h : OCExactPremises sevm pre T dy W W' W'' U P) (F : Nat) :
    OCExactPremises {sevm with gas := F} pre T dy W W' W'' U P := by
  obtain ⟨hs, hb, hp⟩ := h
  exact ⟨hs.withStaticGas F, hb.withStaticGas F, hp.withStaticGas F⟩


/-! ## The model's words are unique

`removeLiquidityOneCoin_live_exact` binds the model's words before the residual gas, pinned by the
model's checks. Two witnesses of those checks are the same words. -/

/-- A fee-loop step's output is determined by its inputs. -/
theorem CwStep.unique {eqk : Prop} {xk D1 D0 y F rk r' r'' : B256}
    (h : CwStep eqk xk D1 D0 y F rk r') (h' : CwStep eqk xk D1 D0 y F rk r'') : r' = r'' := by
  obtain ⟨-, -, dx, hb, -, -, rfl⟩ := h
  obtain ⟨-, -, dx', hb', -, -, rfl⟩ := h'
  rcases hb with ⟨he, -, rfl⟩ | ⟨hn, -, rfl⟩ <;> rcases hb' with ⟨he', -, rfl⟩ | ⟨hn', -, rfl⟩
  · rfl
  · exact absurd he hn'
  · exact absurd he' hn
  · rfl

/-- **The pinned words are unique**: two witnesses of `removeLiquidityOneCoin_live_exact`'s
checks (`aChk`, `xpChk`, `getDChk`, `getYDChk`, `CwStep`) are the same words. -/
theorem ocWords_unique {s : State} {t : Nat} {iw a T F : B256} {hi3 hi3' : iw.toNat < 3}
    {amp amp' : Nat} {x0 x1 x2 D0 y r0 r1 r2 y2 x0' x1' x2' D0' y' r0' r1' r2' y2' : B256}
    (hA : aChk s t = some amp) (hX : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat)
    (hy : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
      (D0 - a * D0 / T).toNat = some y.toNat)
    (h0 : CwStep (Bytes.toB256 [0] = iw) x0 (D0 - a * D0 / T) D0 y F x0 r0)
    (h1 : CwStep (Bytes.toB256 [1] = iw) x1 (D0 - a * D0 / T) D0 y F x1 r1)
    (h2 : CwStep (Bytes.toB256 [2] = iw) x2 (D0 - a * D0 / T) D0 y F x2 r2)
    (hy2 : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
      (D0 - a * D0 / T).toNat = some y2.toNat)
    (hA' : aChk s t = some amp')
    (hX' : xpChk s.balances = some ⟨x0'.toNat, x1'.toNat, x2'.toNat⟩)
    (hD0' : getDChk (V3.mk x0'.toNat x1'.toNat x2'.toNat).get amp' 1 = some D0'.toNat)
    (hy' : getYDChk amp' ⟨iw.toNat, hi3'⟩ (V3.mk x0'.toNat x1'.toNat x2'.toNat).get
      (D0' - a * D0' / T).toNat = some y'.toNat)
    (h0' : CwStep (Bytes.toB256 [0] = iw) x0' (D0' - a * D0' / T) D0' y' F x0' r0')
    (h1' : CwStep (Bytes.toB256 [1] = iw) x1' (D0' - a * D0' / T) D0' y' F x1' r1')
    (h2' : CwStep (Bytes.toB256 [2] = iw) x2' (D0' - a * D0' / T) D0' y' F x2' r2')
    (hy2' : getYDChk amp' ⟨iw.toNat, hi3'⟩ (V3.mk r0'.toNat r1'.toNat r2'.toNat).get
      (D0' - a * D0' / T).toNat = some y2'.toNat) :
    amp = amp' ∧ x0 = x0' ∧ x1 = x1' ∧ x2 = x2' ∧ D0 = D0' ∧ y = y' ∧ r0 = r0' ∧ r1 = r1' ∧
      r2 = r2' ∧ y2 = y2' := by
  obtain rfl : amp = amp' := Option.some.inj (hA.symm.trans hA')
  have hx := Option.some.inj (hX.symm.trans hX')
  simp only [V3.mk.injEq] at hx
  obtain rfl : x0 = x0' := B256.toNat_inj _ _ hx.1
  obtain rfl : x1 = x1' := B256.toNat_inj _ _ hx.2.1
  obtain rfl : x2 = x2' := B256.toNat_inj _ _ hx.2.2
  obtain rfl : D0 = D0' := B256.toNat_inj _ _ (Option.some.inj (hD0.symm.trans hD0'))
  obtain rfl : y = y' := B256.toNat_inj _ _ (Option.some.inj (hy.symm.trans hy'))
  obtain rfl := h0.unique h0'
  obtain rfl := h1.unique h1'
  obtain rfl := h2.unique h2'
  obtain rfl : y2 = y2' := B256.toNat_inj _ _ (Option.some.inj (hy2.symm.trans hy2'))
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Blanc.Lift.Curve3Pool
