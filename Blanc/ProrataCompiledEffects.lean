-- ProrataCompiledEffects.lean : deployed-byte PRORATA body-effect lifts.

import Blanc.ProrataCode
import Blanc.ProrataConsistency

namespace Blanc

open Jaune

namespace Prorata

private theorem installed_prorata_compile {sevm : Sevm}
    (h_code : sevm.code.toList = prorataCode) :
    some sevm.code.toList = Prog.compile Prorata.prorata := by
  calc
    some sevm.code.toList = some prorataCode := congrArg some h_code
    _ = Prog.compile Prorata.prorata := prorataCode_compile.symm

private theorem BodyEntry.of_burn
    {fs : List Func} {sevm : Sevm} {pre entry post : Devm} {body : Func}
    (burn : Devm.Burn pre entry)
    (bodyEntry : BodyEntry fs sevm entry post body) :
    BodyEntry fs sevm pre post body := by
  rcases bodyEntry with ⟨bodyPre, hstor, hbal, hcode, run⟩
  refine ⟨bodyPre, hstor.trans ?_, hbal.trans ?_, hcode.trans ?_, run⟩
  · funext a
    exact burn.getStor a
  · funext a
    exact burn.getBal a
  · change entry.state.getCode = pre.state.getCode
    rw [burn.state]

/-- Every successful invocation of the deployed PRORATA bytecode reaches one
of its five source-level bodies, retaining both persistent entry state and the
shared zero-value fact for each nonpayable route. -/
theorem classify_prorata_exec_route
    {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : sevm.code.toList = prorataCode) :
    ProrataMainRoute (prorata.main :: prorata.aux) sevm pre post := by
  have hrun := correct sevm pre prorata post exc
    (installed_prorata_compile h_code)
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => hentry
  rename (Func.Run _ _ _ _ _) => hmain
  rename (Devm.Burn _ _) => hburn
  rename Devm => entry
  cases hentry
  change Func.Run _ sevm entry prorataMain post at hmain
  rcases classify_prorataMain_route hmain with
    hdeposit | ⟨hvalue, hwithdraw⟩ | ⟨hvalue, hshares⟩ |
      ⟨hvalue, hassets⟩ | hdonate
  · exact .deposit (BodyEntry.of_burn hburn hdeposit)
  · exact .withdraw hvalue (BodyEntry.of_burn hburn hwithdraw)
  · exact .convertToShares hvalue (BodyEntry.of_burn hburn hshares)
  · exact .convertToAssets hvalue (BodyEntry.of_burn hburn hassets)
  · exact .donate (BodyEntry.of_burn hburn hdonate)

/-- Compatibility projection for consumers that only need the five-way
persistent-state body classification. -/
theorem classify_prorata_exec_success
    {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : sevm.code.toList = prorataCode) :
    ProrataMainSuccess (prorata.main :: prorata.aux) sevm pre post := by
  cases classify_prorata_exec_route exc h_code with
  | deposit entry => exact .deposit entry
  | withdraw _ entry => exact .withdraw entry
  | convertToShares _ entry => exact .convertToShares entry
  | convertToAssets _ entry => exact .convertToAssets entry
  | donate entry => exact .donate entry

theorem prorata_deposit_exec_effect
    {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : sevm.code.toList = prorataCode)
    (h_sel : Sevm.selector sevm = selector "deposit" [])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    DepositEffect sevm pre post := by
  rcases exec_enters_prorataSelector_logs exc (installed_prorata_compile h_code)
    h_sel h_nonempty (show (selector "deposit" [], deposit) ∈ prorataFuncs by
      simp [prorataFuncs]) with
    ⟨entry, hstor, hbal, hcodeEntry, hmem, hlogs, hout, run⟩
  have heffect := deposit_effect run
  unfold DepositEffect at heffect ⊢
  dsimp at heffect ⊢
  rw [hstor, hbal, hcodeEntry, hlogs] at heffect
  exact heffect

theorem prorata_withdraw_exec_effect
    {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : sevm.code.toList = prorataCode)
    (h_sel : Sevm.selector sevm = selector "withdraw" [.uint256])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    WithdrawPaysExactly sevm pre post := by
  rcases exec_enters_prorataSelector_logs exc (installed_prorata_compile h_code)
    h_sel h_nonempty (show (selector "withdraw" [.uint256], withdraw) ∈ prorataFuncs by
      simp [prorataFuncs]) with
    ⟨entry, hstor, hbal, hcodeEntry, hmem, hlogs, hout, run⟩
  have heffect := withdraw_pays_exactly run
  unfold WithdrawPaysExactly at heffect ⊢
  dsimp at heffect ⊢
  unfold WithdrawPreCallEffect at heffect ⊢
  dsimp at heffect ⊢
  rw [hstor, hbal, hcodeEntry, hmem, hlogs, hout] at heffect
  exact heffect

theorem prorata_convertToShares_exec_effect
    {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : sevm.code.toList = prorataCode)
    (h_sel : Sevm.selector sevm = selector "convertToShares" [.uint256])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    SharesViewEffect sevm pre post := by
  rcases exec_enters_prorataSelector_logs exc (installed_prorata_compile h_code)
    h_sel h_nonempty (show (selector "convertToShares" [.uint256], convertToShares) ∈ prorataFuncs by
      simp [prorataFuncs]) with
    ⟨entry, hstor, hbal, hcodeEntry, hmem, hlogs, hout, run⟩
  have heffect := convertToShares_effect run
  unfold SharesViewEffect at heffect ⊢
  dsimp at heffect ⊢
  rw [hstor, hbal, hcodeEntry, hlogs] at heffect
  exact heffect

theorem prorata_convertToAssets_exec_effect
    {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : sevm.code.toList = prorataCode)
    (h_sel : Sevm.selector sevm = selector "convertToAssets" [.uint256])
    (h_nonempty : sevm.data.length.toB256 ≠ 0) :
    AssetsViewEffect sevm pre post := by
  rcases exec_enters_prorataSelector_logs exc (installed_prorata_compile h_code)
    h_sel h_nonempty (show (selector "convertToAssets" [.uint256], convertToAssets) ∈ prorataFuncs by
      simp [prorataFuncs]) with
    ⟨entry, hstor, hbal, hcodeEntry, hmem, hlogs, hout, run⟩
  have heffect := convertToAssets_effect run
  unfold AssetsViewEffect at heffect ⊢
  dsimp at heffect ⊢
  rw [hstor, hbal, hcodeEntry, hlogs] at heffect
  exact heffect

/-- Deployed-byte, zero-tolerance preview/deposit agreement. -/
theorem prorata_convertToShares_eq_deposit_mint
    {view depositCall : Sevm} {viewPre viewPost depositPre depositPost : Devm}
    (viewExec : Exec 0 view viewPre (.ok viewPost))
    (depositExec : Exec 0 depositCall depositPre (.ok depositPost))
    (hviewCode : view.code.toList = prorataCode)
    (hdepositCode : depositCall.code.toList = prorataCode)
    (hviewSel : Sevm.selector view = selector "convertToShares" [.uint256])
    (hdepositSel : Sevm.selector depositCall = selector "deposit" [])
    (hviewNonempty : view.data.length.toB256 ≠ 0)
    (hdepositNonempty : depositCall.data.length.toB256 ≠ 0)
    (hTarget : view.currentTarget = depositCall.currentTarget)
    (hStor : Devm.getStor viewPre = Devm.getStor depositPre)
    (hBal : Devm.getBal viewPre view.currentTarget =
      Devm.getBal depositPre depositCall.currentTarget - depositCall.value)
    (hArg : Sevm.argWord view 0 = depositCall.value) :
    ∃ m, m = depositCall.value *
        ((Devm.getStor depositPre depositCall.currentTarget).get supplySlot + offset) /
          ((Devm.getBal depositPre depositCall.currentTarget - depositCall.value) + 1) ∧
      ReturnsWord m viewPost ∧ ReturnsWord m depositPost := by
  have hview := prorata_convertToShares_exec_effect viewExec hviewCode
    hviewSel hviewNonempty
  have hdeposit := prorata_deposit_exec_effect depositExec hdepositCode
    hdepositSel hdepositNonempty
  unfold SharesViewEffect at hview
  unfold DepositEffect at hdeposit
  dsimp at hview hdeposit
  rcases hview with ⟨hv1, hv2, hv3, hviewWord, hv4, hv5, hv6, hv7⟩
  rcases hdeposit with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7, hdepositWord⟩
  refine ⟨depositCall.value *
      ((Devm.getStor depositPre depositCall.currentTarget).get supplySlot + offset) /
        ((Devm.getBal depositPre depositCall.currentTarget - depositCall.value) + 1),
    rfl, ?_, hdepositWord⟩
  rw [hArg, hStor, hBal, hTarget] at hviewWord
  exact hviewWord

/-- Deployed-byte, zero-tolerance preview/withdrawal agreement.  The exact
accepted payout package is retained; no callback-final storage equality is
asserted. -/
theorem prorata_convertToAssets_eq_withdraw_pay
    {view withdrawal : Sevm} {viewPre viewPost withdrawPre withdrawPost : Devm}
    (viewExec : Exec 0 view viewPre (.ok viewPost))
    (withdrawExec : Exec 0 withdrawal withdrawPre (.ok withdrawPost))
    (hviewCode : view.code.toList = prorataCode)
    (hwithdrawCode : withdrawal.code.toList = prorataCode)
    (hviewSel : Sevm.selector view = selector "convertToAssets" [.uint256])
    (hwithdrawSel : Sevm.selector withdrawal = selector "withdraw" [.uint256])
    (hviewNonempty : view.data.length.toB256 ≠ 0)
    (hwithdrawNonempty : withdrawal.data.length.toB256 ≠ 0)
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
  have hview := prorata_convertToAssets_exec_effect viewExec hviewCode
    hviewSel hviewNonempty
  have hpay := prorata_withdraw_exec_effect withdrawExec hwithdrawCode
    hwithdrawSel hwithdrawNonempty
  unfold AssetsViewEffect at hview
  unfold WithdrawPaysExactly at hpay
  dsimp at hview hpay
  rcases hview with ⟨hv1, hv2, hviewWord, hv3, hv4, hv5, hv6⟩
  rcases hpay with ⟨callPre, callPost, guardPost, returnPre, hpre, hpayout, hwithdrawWord⟩
  refine ⟨Sevm.argWord withdrawal 0 *
      (Devm.getBal withdrawPre withdrawal.currentTarget + 1) /
        ((Devm.getStor withdrawPre withdrawal.currentTarget).get supplySlot + offset),
    rfl, ?_, hwithdrawWord.2.2, ?_⟩
  · rw [hArg, hStor, hBal, hTarget] at hviewWord
    exact hviewWord
  · exact ⟨callPre, callPost, guardPost, returnPre, hpre, hpayout, hwithdrawWord⟩

end Prorata

end Blanc
