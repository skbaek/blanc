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
* **The world is a chain of invariants, not a fixed state.** Each later call runs over the world
  the earlier calls left, which only their premises describe. A premise holds at every call-site
  world satisfying `W` and lands in `W'`; `WClosed` asks each invariant to survive the pool's own
  steps (storage reads and writes, logs, identity copies, stack/memory/gas changes). A
  state-changing call with a positive amount (a transfer, a pull, a mint, a burn) must land in a
  fresh invariant: one `W` closed under a positive transfer out of the pool would need unbounded
  balance, so no honest token satisfies `…OkAt W W` there. The liveness theorems therefore take a
  world chain `W 0 → W 1 → …`, one step per state-changing call; static calls stay put. A user
  picks the chain (e.g. "the coins' code is as deployed and the pool's ledger entry in coin `k`
  is at least what is still to be pushed") and proves these facts for concrete callees.

Each premise also asks the stack below the call's operands to leave room for the result flag
(`S.length < 1024`, the identity and code-call steps' own condition): without it a long `S`
admits no successor state and no callee could satisfy the premise.

The premises are stated per call window (`StaticWordOkAt`, `MutCallOkAt`; the call-site
world `W`, the world left `W'`): `SupplyOkAt` (`totalSupply()`), `CoinBalOkAt` (`balanceOf(self)`,
the fee coin's balance-difference path), `CoinPushOkAt` (`transfer`), `CoinPullOkAt`
(`transferFrom`), `BurnOkAt` (`burnFrom`) and `MintOkAt` (`mint`, the input and reply test of
`xa_al_mintCall`). `SupplyOk sevm W t T U` is `remove_liquidity`'s `token.totalSupply()` window
(`STATICCALL`, input at `0x17c`, output at `0x1c0`); its burn window is `BurnOkTo`
(`Walk/RemoveLiquidityLive.lean`).
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

open Jaune Blanc in
/-- **An invariant of the world outside the frame survives the pool's own steps**: whatever reads
only the code everywhere and the storage of accounts other than the pool. -/
theorem WClosed.of_foreign {sevm : Sevm} {P : Devm → Prop}
    (h : ∀ b d, P b → (∀ a, a ≠ sevm.currentTarget → Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → P d) : WClosed sevm P where
  st b _ _ _ hb := h b _ hb (fun _ _ => rfl) (fun _ => rfl)
  sload b k hb := h b _ hb (fun a _ => afterSload_getStor sevm b k a)
    (fun a => afterSload_getCode sevm b k a)
  sstore b k v hb := h b _ hb (fun a ha => afterSstore_getStor_ne sevm b k v a (Ne.symm ha))
    (fun a => afterSstore_getCode sevm b k v a)
  sha b b' _ hp hb := h b b' hb (fun a _ => hp.stor a) (fun a => hp.code a)
  log b _ hb := h b _ hb (fun _ _ => rfl) (fun _ => rfl)

/-! ## Call windows

Every pool call site is a `STATICCALL` or a `CALL` with input window `[ii, ii + is)` and output
window `[oi, oi + 0x20)`, forwarding all the frame's gas. `StaticWordOkAt` and `MutCallOkAt` are
the premises at one window; `W` is the world invariant at the call site and `W'` the one the call
leaves (equal for every call except where a later reply must differ, as `exchange`'s two
`balanceOf(self)` answers around the `transferFrom` pull). -/

/-- **A `STATICCALL` with calldata `data` answers the word `A`** at window `(ii, is, oi)`. -/
def StaticWordOkAt (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes) (A : B256)
    (U : Nat) (ii is oi : B256) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read ii.toNat is.toNat).1 = data → S.length < 1024 →
    ∃ d out, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: ii :: is :: oi :: 0x20 :: S) M G) (.exec .staticcall) d ∧
      StaticCallPost b d S M ii is oi 0x20 1 out ∧ 32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      Bytes.toB256 (out.take 32) = A ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧ W' d ∧
      (IdReady sevm b → IdReady sevm d)

/-- **A value-`0` `CALL` with calldata `data` succeeds** at window `(ii, is, oi)`: the reply
passes `ok`, the pool's storage is kept. -/
def MutCallOkAt (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes)
    (ok : Bytes → Prop) (U : Nat) (ii is oi : B256) : Prop :=
  ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → U ≤ G → G < 2 ^ 256 →
    (M.read ii.toNat is.toNat).1 = data → S.length < 1024 →
    ∃ d, Ninst.RunCompiled sevm
        (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G) (.exec .call) d ∧
      MutableCallPost b d S M ii is oi 0x20 1 ∧ ok d.returnData ∧
      d.returnData.length < 2 ^ 256 ∧ G ≤ d.gasLeft + U ∧ d.gasLeft ≤ G ∧
      d.getStor sevm.currentTarget = b.getStor sevm.currentTarget ∧ W' d ∧
      (IdReady sevm b → IdReady sevm d)

/-- **3Crv's `totalSupply()` answers `T`** at window `(ii, 4, oi)`. -/
abbrev SupplyOkAt (sevm : Sevm) (W W' : Devm → Prop) (t T : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  StaticWordOkAt sevm W W' t totalSupplyData T U ii 4 oi

/-- **`coins[i].balanceOf(self)` answers `B`** at window `(ii, 0x24, oi)` (the fee coin's
balance-difference path). -/
abbrev CoinBalOkAt (sevm : Sevm) (W W' : Devm → Prop) (t B : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  StaticWordOkAt sevm W W' t (balanceOfData sevm.currentTarget) B U ii 0x24 oi

/-- **`coins[i].transfer(msg.sender, amt)` succeeds** at window `(ii, 0x44, oi)`. -/
abbrev CoinPushOkAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  MutCallOkAt sevm W W' t (transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk U
    ii 0x44 oi

/-- **`coins[i].transferFrom(msg.sender, self, amt)` succeeds** at window `(ii, 0x64, oi)`. -/
abbrev CoinPullOkAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  MutCallOkAt sevm W W' t (transferFromSel ++ sevm.caller.toB256.toBytes ++
    sevm.currentTarget.toB256.toBytes ++ amt.toBytes) RawCallOk U ii 0x64 oi

/-- **`token.burnFrom(msg.sender, amt)` succeeds** at window `(ii, 0x44, oi)` with at least 32
bytes back. -/
abbrev BurnOkAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  MutCallOkAt sevm W W' t (burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes)
    (fun r => 32 ≤ r.length) U ii 0x44 oi

/-- **`token.mint(msg.sender, amt)` succeeds** at window `(ii, 0x44, oi)` with at least 32 bytes
back: the input and reply test of `add_liquidity`'s mint site (`xa_al_mintCall`). -/
abbrev MintOkAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  MutCallOkAt sevm W W' t (mintSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes)
    (fun r => 32 ≤ r.length) U ii 0x44 oi

/-! ## `remove_liquidity`'s windows -/

/-- **3Crv's `totalSupply()` answers `T`** (`remove_liquidity`'s window). -/
abbrev SupplyOk (sevm : Sevm) (W : Devm → Prop) (t T : B256) (U : Nat) : Prop :=
  SupplyOkAt sevm W W t T U 0x17c 0x1c0

end Blanc.Lift.Curve3Pool
