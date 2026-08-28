-- ProrataConsistency.lean : occurrence-local body-level PRORATA joins.

import Blanc.ProrataDeposit
import Blanc.ProrataRead
import Blanc.ProrataWithdraw

namespace Blanc

open Jaune

namespace Prorata

/-- At aligned entry observations, the shares preview and deposit return the
same exact EVM word.  The balance alignment accounts for the deposit message
credit already present when the payable body starts. -/
theorem convertToShares_eq_deposit_mint
    {vfs dfs : List Func} {view depositCall : Sevm}
    {viewPre viewPost depositPre depositPost : Devm}
    (viewRun : Func.Run vfs view viewPre convertToShares viewPost)
    (depositRun : Func.Run dfs depositCall depositPre deposit depositPost)
    (hTarget : view.currentTarget = depositCall.currentTarget)
    (hStor : Devm.getStor viewPre = Devm.getStor depositPre)
    (hBal : Devm.getBal viewPre view.currentTarget =
      Devm.getBal depositPre depositCall.currentTarget - depositCall.value)
    (hArg : Sevm.argWord view 0 = depositCall.value) :
    ∃ m, m = depositCall.value *
        ((Devm.getStor depositPre depositCall.currentTarget).get supplySlot + offset) /
          ((Devm.getBal depositPre depositCall.currentTarget - depositCall.value) + 1) ∧
      ReturnsWord m viewPost ∧ ReturnsWord m depositPost := by
  have hview := convertToShares_effect viewRun
  unfold SharesViewEffect at hview
  dsimp at hview
  rcases hview with ⟨hvalue, hbalance, hcap, hviewWord, hstor, hbal', hcode, hlogs⟩
  have hdeposit := deposit_effect depositRun
  unfold DepositEffect at hdeposit
  dsimp at hdeposit
  rcases hdeposit with
    ⟨hdepositValue, hdepositBalance, hdepositCap, hdepositStor, hdepositBal,
      hdepositCode, hdepositLogs, hdepositWord⟩
  refine ⟨depositCall.value *
      ((Devm.getStor depositPre depositCall.currentTarget).get supplySlot + offset) /
        ((Devm.getBal depositPre depositCall.currentTarget - depositCall.value) + 1),
    rfl, ?_, hdepositWord⟩
  rw [hArg, hStor, hBal, hTarget] at hviewWord
  exact hviewWord

/-- At aligned entry observations, the assets preview and the outer successful
withdrawal return the same exact payout word.  `WithdrawPaysExactly` remains
in the conclusion because callback-final storage is deliberately not equated
with the pre-CALL debit state. -/
theorem convertToAssets_eq_withdraw_pay
    {vfs wfs : List Func} {view withdrawal : Sevm}
    {viewPre viewPost withdrawPre withdrawPost : Devm}
    (viewRun : Func.Run vfs view viewPre convertToAssets viewPost)
    (withdrawRun : Func.Run wfs withdrawal withdrawPre withdraw withdrawPost)
    (hTarget : view.currentTarget = withdrawal.currentTarget)
    (hStor : Devm.getStor viewPre = Devm.getStor withdrawPre)
    (hBal : Devm.getBal viewPre view.currentTarget =
      Devm.getBal withdrawPre withdrawal.currentTarget)
    (hArg : Sevm.argWord view 0 = Sevm.argWord withdrawal 0) :
    ∃ p, p = Sevm.argWord withdrawal 0 *
        (Devm.getBal withdrawPre withdrawal.currentTarget + 1) /
          ((Devm.getStor withdrawPre withdrawal.currentTarget).get supplySlot + offset) ∧
      ReturnsWord p viewPost ∧ ReturnsWord p withdrawPost ∧
      WithdrawPaysExactly withdrawal withdrawPre withdrawPost := by
  have hview := convertToAssets_effect viewRun
  unfold AssetsViewEffect at hview
  dsimp at hview
  rcases hview with ⟨hshares, hbalance, hviewWord, hstor, hbal', hcode, hlogs⟩
  have hpay := withdraw_pays_exactly withdrawRun
  unfold WithdrawPaysExactly at hpay
  dsimp at hpay
  rcases hpay with ⟨callPre, callPost, guardPost, returnPre, hpre, hpayout, hwithdrawWord⟩
  refine ⟨Sevm.argWord withdrawal 0 *
      (Devm.getBal withdrawPre withdrawal.currentTarget + 1) /
        ((Devm.getStor withdrawPre withdrawal.currentTarget).get supplySlot + offset),
    rfl, ?_, hwithdrawWord, ?_⟩
  · rw [hArg, hStor, hBal, hTarget] at hviewWord
    exact hviewWord
  · exact ⟨callPre, callPost, guardPost, returnPre, hpre, hpayout, hwithdrawWord⟩

end Prorata

end Blanc
