import Blanc.Lift.Curve3Pool.Walk.LiveKit
import Blanc.Lift.StaticCall
import Blanc.Lift.MutableCallPost

/-!
# The pool's liveness premises: what its callees must do

A pool frame calls 3Crv and the coins. Its liveness holds only when those calls succeed, so each
call site carries a premise in the shape of WETH9's `SendOk` and 3Crv's `OwnerCallOk`: made from
the call site with enough gas and the right input window, the call succeeds and leaves the
caller what it needs.

Two choices make the premises satisfiable by real callees:

* **Gas is relative.** A `CALL` forwards almost all the caller's gas, so a callee given `G`
  cannot leave a fixed amount above what the caller still needs for the next call. Each
  premise bounds the gas the call *uses*: from `G ≥ U` it leaves at least `G - U` (and at most
  `G`).
* **The world is an invariant `W`, not a fixed state.** Each later call runs over the world the
  earlier calls left, which only their premises describe. A premise holds at every call-site
  world satisfying `W` and re-establishes `W`; `WClosed` asks `W` to survive the pool's own steps
  (storage reads and writes, logs, identity copies, stack/memory/gas changes). A user picks `W`
  (e.g. "the pool holds enough of each coin, the coins' code is as deployed") and proves these
  facts for concrete callees.

* `SupplyOk sevm W t T U`: `token.totalSupply()` (`STATICCALL`, input at `0x17c`, output at
  `0x1c0`) answers the word `T` in at least 32 bytes;
* `CoinPushOk sevm W t amt U`: `coins[i].transfer(msg.sender, amt)` (`CALL`, input at `0x520`,
  output window `0x5c0`) succeeds, its reply passes `RawCallOk`, and the pool's storage is kept;
* `BurnOk sevm W t amt U`: `token.burnFrom(msg.sender, amt)` (`CALL`, input at `0x61c`, output
  at `0x6a0`) succeeds with at least 32 bytes and the pool's storage kept.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`W` survives the pool's own steps.** -/
structure WClosed (sevm : Sevm) (W : Devm → Prop) : Prop where
  st : ∀ b S M G, W b → W (St b S M G)
  sload : ∀ b k, W b → W (afterSload sevm b k)
  sstore : ∀ b k v, W b → W (afterSstore sevm b k v)
  sha : ∀ b b' rd, ShaCallPost b b' rd → W b → W b'
  log : ∀ b l, W b → W (b.addLog l)

/-- **3Crv's `totalSupply()` answers `T`.** -/
def SupplyOk (sevm : Sevm) (W : Devm → Prop) (t T : B256) (U : Nat) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read 0x17c 4).1 = totalSupplyData →
    ∃ d out, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: 0x17c :: 4 :: 0x1c0 :: 0x20 :: S) M G) (.exec .staticcall) d ∧
      StaticCallPost b d S M 0x17c 4 0x1c0 0x20 1 out ∧ 32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      Bytes.toB256 (out.take 32) = T ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧ W d ∧
      (IdReady sevm b → IdReady sevm d)

/-- **`coins[i].transfer(msg.sender, amt)` succeeds.** -/
def CoinPushOk (sevm : Sevm) (W : Devm → Prop) (t amt : B256) (U : Nat) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read 0x520 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes →
    ∃ d, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: 0 :: 0x520 :: 0x44 :: 0x5c0 :: 0x20 :: S) M G) (.exec .call) d ∧
      MutableCallPost b d S M 0x520 0x44 0x5c0 0x20 1 ∧ RawCallOk d.returnData ∧
      d.returnData.length < 2 ^ 256 ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W d ∧
      (IdReady sevm b → IdReady sevm d)

/-- **`token.burnFrom(msg.sender, amt)` succeeds.** -/
def BurnOk (sevm : Sevm) (W : Devm → Prop) (t amt : B256) (U : Nat) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read 0x61c 0x44).1 = burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes →
    ∃ d, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: 0 :: 0x61c :: 0x44 :: 0x6a0 :: 0x20 :: S) M G) (.exec .call) d ∧
      MutableCallPost b d S M 0x61c 0x44 0x6a0 0x20 1 ∧ 32 ≤ d.returnData.length ∧
      d.returnData.length < 2 ^ 256 ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W d

end Blanc.Lift.Curve3Pool
