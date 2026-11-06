import Blanc.Lift.Curve3Pool.Decode

/-!
# The entries whose model step makes no call

`Call.free`: not one of the six entries that move coins or 3Crv. `step_calls_nil`: an accepted step of any
other entry names no external call, and `decodeCall_free`: a selector among `callFreeSels` decodes to such
an entry.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- Not one of the six entries that call a coin or 3Crv state-changingly. -/
def Call.free : Call → Bool
  | .addLiquidity .. | .exchange .. | .removeLiquidity .. | .removeLiquidityImbalance ..
  | .removeLiquidityOneCoin .. | .withdrawAdminFees => false
  | _ => true

/-- **An accepted step of a call-free entry names no external call.** -/
theorem step_calls_nil {s : State} {e : Env} {c : Call} {o : Out} (hc : c.free = true)
    (h : step s e c = some o) : o.calls = [] := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · cases c <;> first
        | exact Bool.noConfusion hc
        | (simp only [body, viewOut, rampA, stopRampA, commitNewFee, applyNewFee, revertNewParameters,
            commitTransferOwnership, applyTransferOwnership, revertTransferOwnership, donateAdminFees,
            killMe, unkillMe, req, bind, Option.bind, pure] at h
           repeat' (first | (dsimp only at h; split at h) | split at h)
           all_goals first
             | (cases h <;> rfl)
             | (dsimp only at h; cases h <;> rfl))
    · cases h

/-- The selectors of the call-free entries, in dispatcher order. -/
def callFreeSels : List B256 :=
  [selA, selGetVirtualPrice, selCalcTokenAmount, selGetDy, selGetDyUnderlying, selCalcWithdrawOneCoin,
    selRampA, selStopRampA, selCommitNewFee, selApplyNewFee, selRevertNewParameters,
    selCommitTransferOwnership, selApplyTransferOwnership, selRevertTransferOwnership, selAdminBalances,
    selDonateAdminFees, selKillMe, selUnkillMe, selCoins, selBalances, selFee, selAdminFee, selOwner,
    selInitialA, selFutureA, selInitialATime, selFutureATime, selAdminActionsDeadline,
    selTransferOwnershipDeadline, selFutureFee, selFutureAdminFee, selFutureOwner]

theorem callAt_free (sevm : Sevm) {k : Nat} (hk : k ∉ [3, 6, 7, 8, 10, 20]) :
    (callAt sevm k).free = true := by
  unfold callAt
  split <;> first | rfl | exact absurd (by decide) hk

theorem callFreeSels_findIdx :
    ∀ sel ∈ callFreeSels, (sels.findIdx? (· = sel)).all (fun k => decide (k ∉ [3, 6, 7, 8, 10, 20])) = true := by
  decide +kernel

/-- **A selector among `callFreeSels` decodes to a call-free entry.** -/
theorem decodeCall_free {sevm : Sevm} (hlen : 4 ≤ sevm.data.length) (hin : Sevm.selector sevm ∈ callFreeSels) :
    (decodeCall sevm).free = true := by
  have hall := callFreeSels_findIdx _ hin
  rw [decodeCall, if_neg (by omega)]
  split
  · rename_i k hk
    rw [hk] at hall
    exact callAt_free sevm (of_decide_eq_true hall)
  · rfl

end Blanc.Lift.Curve3Pool
