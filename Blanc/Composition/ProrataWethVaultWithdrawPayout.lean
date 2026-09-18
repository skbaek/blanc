-- ProrataWethVaultWithdrawPayout.lean : WETH `withdraw` split at its accepted payout.

import Blanc.Composition.ProrataWethVaultHistory

/-!
# WETH `withdraw` at its accepted payout

The pair history's WETH `withdraw` segment hypothesis,
`WethWithdrawAcceptedPayout`, discharged.  `weth_withdraw_preCall_split`
supplies the debited storage, the seven payout operands and the nonzero success
word; this module opens the `CALL` with `of_run_call_val_with_depth_frame`,
builds the accepted payout trace with the exact child message in hand, and
hands WETH's own precondition to the callback entry through the outbound value
transfer.  Nothing is said about the callback's behaviour.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-- **WETH `withdraw` splits at its accepted payout.**  Every committed compiled
`withdraw` entered under WETH's precondition by a caller other than WETH
exposes its accepted payout `CALL`, the storage written before it, and the
callback entry's inherited code, block statics and WETH precondition. -/
theorem wethWithdrawAcceptedPayout : WethWithdrawAcceptedPayout := by
  intro sevm pre post run target _ callerNe selected precondition _
  obtain ⟨callPre, callPost, -, written, foreignKept, callRun, after, callStack,
    callBal, callCode, solvent, success, guardPost, nonzero, successPop⟩ :=
    weth_withdraw_preCall_split run selected
  rcases of_run_call_val_with_depth_frame (xs := []) callStack callRun with
    failed | callFacts
  · exact absurd (popBurn_pref successPop failed.1).1 nonzero
  exact WethWithdrawSplit.ofCallFacts target callerNe precondition written foreignKept
    callFacts callBal callCode solvent after

end Blanc.Composition.ProrataWethVault
