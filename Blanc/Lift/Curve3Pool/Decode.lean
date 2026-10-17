import Blanc.Lift.Curve3Pool.Layout

/-!
# What a 3pool frame asks: the decoded call

* `sels`: the 38 selectors in the deployed dispatcher's order (U0 `selectors.txt`; the order of
  the `PUSH4 sel; PUSH1 0; MLOAD; EQ; ISZERO; PUSH2 next; JUMPI` tests in the runtime, which is
  the source order and the order of `Model.Call`'s constructors);
* `callAt sevm k`: the model call body `k` implements, its arguments the raw ABI head words of
  the calldata read as numbers (`arg`);
* `decodeCall sevm`: the call the dispatcher selects. Calldata shorter than four bytes, or a
  selector that is none of the 38, is `.other` (the runtime reverts on both: `CALLDATASIZE < 4`
  jumps to the fallback, and the last missed test falls through to it; there is no
  `__default__`);
* `decodeCall_at`, `decodeCall_short`, `decodeCall_miss`: the facts the dispatcher walk needs —
  a hit on test `k` selects `callAt sevm k`, and a short calldata or a miss on every test selects
  `.other`;
* `IsWriter`: the 17 non-view entries (the nonpayable functions of the ABI).

Arguments are raw words: Vyper 0.2.4's clamps (`address < 2^160`, `int128` range, `bool < 2`)
and index checks are part of the model (`idx`, `req (d < 2)`, the address `req`s), not of the
decoder.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-! ## Selectors (dispatcher order) -/

def selA : B256 := 0xf446c1d0
def selGetVirtualPrice : B256 := 0xbb7b8b80
def selCalcTokenAmount : B256 := 0x3883e119
def selAddLiquidity : B256 := 0x4515cef3
def selGetDy : B256 := 0x5e0d443f
def selGetDyUnderlying : B256 := 0x07211ef7
def selExchange : B256 := 0x3df02124
def selRemoveLiquidity : B256 := 0xecb586a5
def selRemoveLiquidityImbalance : B256 := 0x9fdaea0c
def selCalcWithdrawOneCoin : B256 := 0xcc2b27d7
def selRemoveLiquidityOneCoin : B256 := 0x1a4d01d2
def selRampA : B256 := 0x3c157e64
def selStopRampA : B256 := 0x551a6588
def selCommitNewFee : B256 := 0x5b5a1467
def selApplyNewFee : B256 := 0x4f12fe97
def selRevertNewParameters : B256 := 0x226840fb
def selCommitTransferOwnership : B256 := 0x6b441a40
def selApplyTransferOwnership : B256 := 0x6a1c05ae
def selRevertTransferOwnership : B256 := 0x86fbf193
def selAdminBalances : B256 := 0xe2e7d264
def selWithdrawAdminFees : B256 := 0x30c54085
def selDonateAdminFees : B256 := 0x524c3901
def selKillMe : B256 := 0xe3698853
def selUnkillMe : B256 := 0x3046f972
def selCoins : B256 := 0xc6610657
def selBalances : B256 := 0x4903b0d1
def selFee : B256 := 0xddca3f43
def selAdminFee : B256 := 0xfee3f7f9
def selOwner : B256 := 0x8da5cb5b
def selInitialA : B256 := 0x5409491a
def selFutureA : B256 := 0xb4b577ad
def selInitialATime : B256 := 0x2081066c
def selFutureATime : B256 := 0x14052288
def selAdminActionsDeadline : B256 := 0x405e28f8
def selTransferOwnershipDeadline : B256 := 0xe0a0b586
def selFutureFee : B256 := 0x58680d0b
def selFutureAdminFee : B256 := 0xe3824462
def selFutureOwner : B256 := 0x1ec0cdc1

/-- The 38 selectors, in the order the dispatcher tests them. -/
def sels : List B256 :=
  [selA, selGetVirtualPrice, selCalcTokenAmount, selAddLiquidity, selGetDy, selGetDyUnderlying,
    selExchange, selRemoveLiquidity, selRemoveLiquidityImbalance, selCalcWithdrawOneCoin,
    selRemoveLiquidityOneCoin, selRampA, selStopRampA, selCommitNewFee, selApplyNewFee,
    selRevertNewParameters, selCommitTransferOwnership, selApplyTransferOwnership,
    selRevertTransferOwnership, selAdminBalances, selWithdrawAdminFees, selDonateAdminFees,
    selKillMe, selUnkillMe, selCoins, selBalances, selFee, selAdminFee, selOwner, selInitialA,
    selFutureA, selInitialATime, selFutureATime, selAdminActionsDeadline,
    selTransferOwnershipDeadline, selFutureFee, selFutureAdminFee, selFutureOwner]

theorem sels_length : sels.length = 38 := rfl

/-! ## Arguments -/

/-- The `k`-th ABI head word of the calldata, as a number. -/
def arg (sevm : Sevm) (k : B256) : Nat := (Sevm.argWord sevm k).toNat

/-- Three consecutive head words `k, k+1, k+2` (a `uint256[3]` argument). -/
def argV3 (sevm : Sevm) (k : B256) : V3 := ⟨arg sevm k, arg sevm (k + 1), arg sevm (k + 2)⟩

/-- The model call body `k` (dispatcher order) implements, with its raw arguments. -/
def callAt (sevm : Sevm) : Nat → Call
  | 0 => .a
  | 1 => .getVirtualPrice
  | 2 => .calcTokenAmount (argV3 sevm 0) (arg sevm 3)
  | 3 => .addLiquidity (argV3 sevm 0) (arg sevm 3)
  | 4 => .getDy (arg sevm 0) (arg sevm 1) (arg sevm 2)
  | 5 => .getDyUnderlying (arg sevm 0) (arg sevm 1) (arg sevm 2)
  | 6 => .exchange (arg sevm 0) (arg sevm 1) (arg sevm 2) (arg sevm 3)
  | 7 => .removeLiquidity (arg sevm 0) (argV3 sevm 1)
  | 8 => .removeLiquidityImbalance (argV3 sevm 0) (arg sevm 3)
  | 9 => .calcWithdrawOneCoin (arg sevm 0) (arg sevm 1)
  | 10 => .removeLiquidityOneCoin (arg sevm 0) (arg sevm 1) (arg sevm 2)
  | 11 => .rampA (arg sevm 0) (arg sevm 1)
  | 12 => .stopRampA
  | 13 => .commitNewFee (arg sevm 0) (arg sevm 1)
  | 14 => .applyNewFee
  | 15 => .revertNewParameters
  | 16 => .commitTransferOwnership (arg sevm 0)
  | 17 => .applyTransferOwnership
  | 18 => .revertTransferOwnership
  | 19 => .adminBalances (arg sevm 0)
  | 20 => .withdrawAdminFees
  | 21 => .donateAdminFees
  | 22 => .killMe
  | 23 => .unkillMe
  | 24 => .coins (arg sevm 0)
  | 25 => .balances (arg sevm 0)
  | 26 => .fee
  | 27 => .adminFee
  | 28 => .owner
  | 29 => .initialA
  | 30 => .futureA
  | 31 => .initialATime
  | 32 => .futureATime
  | 33 => .adminActionsDeadline
  | 34 => .transferOwnershipDeadline
  | 35 => .futureFee
  | 36 => .futureAdminFee
  | 37 => .futureOwner
  | _ => .other

/-- **The call the deployed dispatcher selects.** -/
def decodeCall (sevm : Sevm) : Call :=
  if sevm.data.length < 4 then .other else
  match sels.findIdx? (· = Sevm.selector sevm) with
  | some k => callAt sevm k
  | none => .other

/-! ## Dispatcher facts -/

/-- Each selector's first occurrence is its own position (the 38 are distinct). -/
theorem sels_findIdx : ∀ k < 38, sels.findIdx? (· = sels[k]!) = some k := by decide +kernel

/-- **A hit on test `k`** selects body `k`'s call. -/
theorem decodeCall_at {sevm : Sevm} {k : Nat} {sel : B256} (hs : sels[k]? = some sel)
    (hsel : Sevm.selector sevm = sel) (hlen : 4 ≤ sevm.data.length) :
    decodeCall sevm = callAt sevm k := by
  have hk : k < 38 := by
    have := (List.getElem?_eq_some_iff.mp hs).1
    rwa [sels_length] at this
  have hget : sels[k]! = sel := by
    rw [List.getElem!_eq_getElem?_getD, hs, Option.getD_some]
  have hlen' : ¬ sevm.data.length < 4 := by omega
  simp only [decodeCall, hlen', ↓reduceIte, hsel, ← hget, sels_findIdx k hk]

/-- **Short calldata** selects `.other`. -/
theorem decodeCall_short {sevm : Sevm} (hlen : sevm.data.length < 4) : decodeCall sevm = .other := by
  simp only [decodeCall, hlen, ↓reduceIte]

/-- **A miss on every test** selects `.other`. -/
theorem decodeCall_miss {sevm : Sevm} (hmiss : ∀ s ∈ sels, Sevm.selector sevm ≠ s) :
    decodeCall sevm = .other := by
  have hnone : sels.findIdx? (· = Sevm.selector sevm) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro s hs
    exact decide_eq_false (Ne.symm (hmiss s hs))
  unfold decodeCall
  split
  · rfl
  · rw [hnone]

/-! ## Writers -/

/-- The 17 non-view entries: the only ones whose model step can change the state, log, or make
a state-changing call. -/
def IsWriter : Call → Prop
  | .addLiquidity _ _ | .exchange _ _ _ _ | .removeLiquidity _ _
  | .removeLiquidityImbalance _ _ | .removeLiquidityOneCoin _ _ _ | .rampA _ _ | .stopRampA
  | .commitNewFee _ _ | .applyNewFee | .revertNewParameters | .commitTransferOwnership _
  | .applyTransferOwnership | .revertTransferOwnership | .withdrawAdminFees | .donateAdminFees
  | .killMe | .unkillMe => True
  | _ => False

end Blanc.Lift.Curve3Pool
