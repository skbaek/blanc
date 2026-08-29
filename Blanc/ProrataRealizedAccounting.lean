-- ProrataRealizedAccounting.lean : configured-history PRORATA accounting.

import Blanc.ProrataDeploymentRoot
import Blanc.ProrataCompiledEffects
import Blanc.ProrataAccounting
import Blanc.ExecutionHistoryStateTrace
import Blanc.ExecutionOccurrence

namespace Blanc

open Jaune

namespace Prorata

namespace AccountingSnapshot

/-- The public PRORATA accounting projection of one exact world state. -/
def ofState (ca : Adr) (state : State) : AccountingSnapshot :=
  ⟨supplyN (state.getStor ca), (state.bal ca).toNat⟩

/-- The semantic pre-credit snapshot at an entered value-carrying message. -/
def beforeCredit (ca : Adr) (value : B256) (state : State) :
    AccountingSnapshot :=
  ⟨supplyN (state.getStor ca), (state.bal ca).toNat - value.toNat⟩

end AccountingSnapshot

/-- Exact invocation identity plus settlement retention exposes the richer
deployed-byte route classification on the retained frame itself. -/
theorem exactInvocation_route
    {ca : Adr} {frame : Exec.Frame}
    (invocation : frame.exactInvocation prorata ca ca) :
    ProrataMainRoute (prorata.main :: prorata.aux)
      frame.sevm frame.pre frame.post := by
  rcases frame with ⟨pc, sevm, pre, out, run, committed⟩
  rcases invocation with ⟨hpc, htarget, haddress, hcode⟩
  change pc = 0 at hpc
  change sevm.currentTarget = ca at htarget
  change sevm.codeAddress = some ca at haddress
  change some sevm.code.toList = Prog.compile prorata at hcode
  change ProrataMainRoute (prorata.main :: prorata.aux) sevm pre
    (Execution.committedPost out committed)
  subst pc
  cases out with
  | error error =>
      simp [Execution.commits] at committed
  | ok post =>
      apply classify_prorata_exec_route run
      apply Option.some.inj
      exact hcode.trans prorataCode_compile

/-- A successful deposit frame is exactly one accounting deposit from the
semantic pre-credit snapshot to the retained frame post-state. -/
theorem DepositEffect.accountingEffect
    {sevm : Sevm} {pre post : Devm}
    (effect : DepositEffect sevm pre post)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget)) :
    ∃ minted,
      ProrataAccountingEffect offset.toNat
        (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
        (.deposit sevm.value.toNat minted)
        (AccountingSnapshot.ofState sevm.currentTarget post.state) := by
  let stor := Devm.getStor pre sevm.currentTarget
  let balance := Devm.getBal pre sevm.currentTarget
  let supply := stor.get supplySlot
  let preBalance := balance - sevm.value
  let minted := sevm.value * (supply + offset) / (preBalance + 1)
  change sevm.value ≤ maxValue ∧ preBalance ≤ maxBalance ∧
    supply + minted ≤ maxSupply ∧
    Devm.getStor post sevm.currentTarget =
      (stor.set supplySlot (supply + minted)).set sevm.caller.toB256
        (stor.get sevm.caller.toB256 + minted) ∧
    Devm.getBal post = Devm.getBal pre ∧
    Devm.getCode post = Devm.getCode pre ∧
    post.logs = pre.logs ∧ ReturnsWord minted post at effect
  rcases effect with
    ⟨hvalue, hbalance, hsupply, hstor, hbal, -, -, -⟩
  have hvalueBalance : sevm.value ≤ balance :=
    B256.le_of_toNat_le_toNat invariant.value_le_balance
  have hmintNof : B256.Nof supply minted := by
    simpa only [minted, supply, preBalance, balance, stor] using
      invariant.deposit_mint_nof hvalue hbalance
  have hquote :
      minted.toNat = mintN offset.toNat sevm.value.toNat
        (supplyN stor) (balance.toNat - sevm.value.toNat) := by
    have quote := deposit_quote_toNat hvalue invariant.supply_word_le hbalance
    rw [B256.toNat_sub_eq_of_le _ _ hvalueBalance] at quote
    simpa only [minted, supply, preBalance, balance, stor, supplyN] using quote
  have hpostSupply :
      supplyN (Devm.getStor post sevm.currentTarget) =
        supplyN stor + minted.toNat := by
    rw [hstor]
    unfold supplyN
    rw [Stor.get_prorataSupplySlot_set (validAdr_toB256 sevm.caller)]
    rw [Stor.get_set_self]
    rw [B256.toNat_add_eq_of_nof _ _ hmintNof]
  have hpostBalance :
      (post.state.bal sevm.currentTarget).toNat =
        (balance.toNat - sevm.value.toNat) + sevm.value.toNat := by
    calc
      (post.state.bal sevm.currentTarget).toNat =
          balance.toNat :=
        congrArg B256.toNat (congrFun hbal sevm.currentTarget)
      _ = (balance.toNat - sevm.value.toNat) + sevm.value.toNat :=
        (Nat.sub_add_cancel invariant.value_le_balance).symm
  refine ⟨minted.toNat, ?_⟩
  rw [show AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
      pre.state =
        ⟨supplyN stor, balance.toNat - sevm.value.toNat⟩ from rfl]
  rw [show AccountingSnapshot.ofState sevm.currentTarget post.state =
      ⟨supplyN stor + minted.toNat,
        (balance.toNat - sevm.value.toNat) + sevm.value.toNat⟩ from by
      exact congrArg₂ AccountingSnapshot.mk hpostSupply hpostBalance]
  exact .deposit _ _ _ _ hquote

/-- The deposit accounting effect survives the dispatcher's persistent-state
silent walk from retained frame entry to the raw source body. -/
theorem BodyEntry.depositAccountingEffect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post deposit)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget)) :
    ∃ minted,
      ProrataAccountingEffect offset.toNat
        (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
        (.deposit sevm.value.toNat minted)
        (AccountingSnapshot.ofState sevm.currentTarget post.state) := by
  rcases entry with ⟨bodyPre, hstor, hbal, hcode, run⟩
  have bodyInvariant :
      Inv (Devm.getStor bodyPre sevm.currentTarget) sevm.value
        (Devm.getBal bodyPre sevm.currentTarget) := by
    rw [hstor, hbal]
    exact invariant
  rcases (deposit_effect run).accountingEffect bodyInvariant with
    ⟨minted, accounting⟩
  refine ⟨minted, ?_⟩
  have hpre :
      AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
          bodyPre.state =
        AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state := by
    unfold AccountingSnapshot.beforeCredit
    exact congrArg₂ AccountingSnapshot.mk
      (congrArg supplyN (congrFun hstor sevm.currentTarget))
      (congrArg (fun balance : B256 =>
        balance.toNat - sevm.value.toNat)
        (congrFun hbal sevm.currentTarget))
  rw [← hpre]
  exact accounting

/-- The settled withdrawal prefix plus its exact paid boundary is precisely
one accounting withdrawal.  Callback state is deliberately outside this
effect; nested retained frames begin after `paidState`. -/
theorem WithdrawPreCallEffect.accountingEffect
    {sevm : Sevm} {pre callPre : Devm} {paidState : State}
    (effect : WithdrawPreCallEffect sevm pre callPre)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget))
    (hpaidStor :
      paidState.getStor sevm.currentTarget =
        Devm.getStor callPre sevm.currentTarget)
    (hpaidBal :
      paidState.bal sevm.currentTarget =
        Devm.getBal pre sevm.currentTarget -
          (Sevm.argWord sevm 0 *
            (Devm.getBal pre sevm.currentTarget + 1) /
              ((Devm.getStor pre sevm.currentTarget).get supplySlot + offset))) :
    ProrataAccountingEffect offset.toNat
      (AccountingSnapshot.ofState sevm.currentTarget pre.state)
      (.withdraw (Sevm.argWord sevm 0).toNat
        (Sevm.argWord sevm 0 *
          (Devm.getBal pre sevm.currentTarget + 1) /
            ((Devm.getStor pre sevm.currentTarget).get supplySlot + offset)).toNat)
      (AccountingSnapshot.ofState sevm.currentTarget paidState) := by
  let shares := Sevm.argWord sevm 0
  let stor := Devm.getStor pre sevm.currentTarget
  let balance := Devm.getBal pre sevm.currentTarget
  let callerShares := stor.get sevm.caller.toB256
  let supply := stor.get supplySlot
  let paid := shares * (balance + 1) / (supply + offset)
  change shares ≤ callerShares ∧ balance ≤ maxBalance ∧
    Devm.getStor callPre sevm.currentTarget =
      (stor.set sevm.caller.toB256 (callerShares - shares)).set
        supplySlot (supply - shares) ∧
    Devm.getBal callPre = Devm.getBal pre ∧
    Devm.getCode callPre = Devm.getCode pre ∧
    callPre.logs = pre.logs ∧ callPre.output = pre.output ∧
    callPre.memory = pre.memory ∧ ∃ gasWord,
      gasWord :: sevm.caller.toB256 :: paid :: 0 :: 0 :: 0 :: 0 :: paid ::
        supply :: (supply + offset) :: shares :: supplySlot :: [] <<+
          callPre.stack at effect
  rcases effect with
    ⟨hcover, hbalance, hstor, -, -, -, -, -, -⟩
  have hsharesSupply : shares ≤ supply :=
    hcover.trans (invariant.share_word_le_supply sevm.caller)
  have hsharesCap : shares ≤ maxSupply :=
    hsharesSupply.trans invariant.supply_word_le
  have hpaidBalance : paid ≤ balance := by
    simpa only [paid, shares, balance, supply, callerShares] using
      invariant.withdraw_pay_word_le_balance sevm.caller hcover hbalance
  have hquote :
      paid.toNat = payN offset.toNat shares.toNat
        (supplyN stor) balance.toNat := by
    have quote := withdraw_quote_toNat hsharesCap invariant.supply_word_le
      hbalance
    simpa only [paid, shares, balance, supply, stor, supplyN] using quote
  have hpostSupply :
      supplyN (paidState.getStor sevm.currentTarget) =
        supplyN stor - shares.toNat := by
    rw [hpaidStor, hstor]
    unfold supplyN
    rw [Stor.get_set_self]
    rw [B256.toNat_sub_eq_of_le _ _ hsharesSupply]
  have hpostBalance :
      (paidState.bal sevm.currentTarget).toNat =
        balance.toNat - paid.toNat := by
    rw [hpaidBal]
    exact B256.toNat_sub_eq_of_le _ _ hpaidBalance
  rw [show AccountingSnapshot.ofState sevm.currentTarget pre.state =
      ⟨supplyN stor, balance.toNat⟩ from rfl]
  rw [show AccountingSnapshot.ofState sevm.currentTarget paidState =
      ⟨supplyN stor - shares.toNat, balance.toNat - paid.toNat⟩ from by
      exact congrArg₂ AccountingSnapshot.mk hpostSupply hpostBalance]
  exact .withdraw _ _ _ _
    (B256.toNat_le_toNat hsharesSupply) hquote

/-- The exact child-message entry selected by an accepted withdrawal payout.
This packages the semantic paid boundary separately from the callback-final
state, together with the retained child trace needed for recursive replay. -/
structure AcceptedPayoutTrace
    (sevm : Sevm) (paid : B256) (callPre callPost : Devm) where
  childMsg : Msg
  entry : Benv
  child : Devm
  trace : ExecutionTrace.ProcessMessageTrace childMsg (.ok child)
  messageState : childMsg.benv.state = callPre.state
  shouldTransferValue : childMsg.shouldTransferValue = true
  caller : childMsg.caller = sevm.currentTarget
  value : childMsg.value = paid
  target : childMsg.currentTarget = sevm.caller.toB256.toAdr
  entryTransfer : childMsg.benvAfterTransfer = .ok entry
  entryStor : entry.state.getStor sevm.currentTarget =
    callPre.state.getStor sevm.currentTarget
  entryBalance : entry.state.bal sevm.currentTarget =
    callPre.state.bal sevm.currentTarget - paid
  callPostState : callPost.state = child.state

/-- An accepted payout to a recipient distinct from PRORATA exposes its
immediate post-transfer entry state and the exact retained callback trace. -/
theorem AcceptedPayout.exists_trace
    {sevm : Sevm} {paid : B256}
    {callPre callPost guardPost returnPre : Devm}
    (payout : AcceptedPayout sevm paid callPre callPost guardPost returnPre)
    (recipient_ne : sevm.caller.toB256.toAdr ≠ sevm.currentTarget) :
    Nonempty (AcceptedPayoutTrace sevm paid callPre callPost) := by
  rcases payout with
    ⟨gasWord, xs, parent, child, xl, delegated, nextAddress, code, avail, pc,
      hstack, hcall, hpop, hburn, hstep, hdepth, hstackEq, hparentState,
      hparentMemory, hparentLogs, hparentOutput, hdelegation, hfilled, hpm,
      hclean, hresume, hcallPostState, hreturnData, hmemory, hpostStack⟩
  let childMsg :=
    callMsg sevm parent
      (min gasWord.toNat (except64th avail) +
        (if paid.toNat = 0 then 0 else gCallStipend))
      paid sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
      ((callPre.memory.read 0 0).1) code delegated
  change ProcessMessage childMsg xl (.ok child) at hpm
  rcases ExecutionTrace.exists_retainedXlot_of_filled hfilled with
    ⟨retained⟩
  let trace : ExecutionTrace.ProcessMessageTrace childMsg (.ok child) :=
    ⟨xl, retained, hpm⟩
  have hmessageState : childMsg.benv.state = callPre.state := by
    change parent.state = callPre.state
    exact hparentState
  have hshouldTransfer : childMsg.shouldTransferValue = true := rfl
  have hcaller : childMsg.caller = sevm.currentTarget := rfl
  have hvalue : childMsg.value = paid := rfl
  have htarget :
      childMsg.currentTarget = sevm.caller.toB256.toAdr := rfl
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases htransfer : childMsg.benvAfterTransfer with error | entry <;>
    rw [htransfer] at hbody
  · rw [hbody.2, processMessage.settle_error] at hset
    cases hset
  · rcases of_benvAfterTransfer hshouldTransfer htransfer with
      ⟨debited, hsub, hentry⟩
    rw [hmessageState, hcaller, hvalue] at hsub
    have hentryState :
        entry.state = debited.addBal sevm.caller.toB256.toAdr paid := by
      rw [hentry, htarget, hvalue]
      rfl
    have fields := of_state_transfer_fields
      (callee := sevm.caller.toB256.toAdr) hsub
    have hentryStor :
        entry.state.getStor sevm.currentTarget =
          callPre.state.getStor sevm.currentTarget := by
      rw [hentryState]
      exact fields.1 sevm.currentTarget
    have hentryBalance :
        entry.state.bal sevm.currentTarget =
          callPre.state.bal sevm.currentTarget - paid := by
      rw [hentryState]
      exact fields.2.2.2.2 recipient_ne
    exact ⟨⟨childMsg, entry, child, trace, hmessageState,
      hshouldTransfer, hcaller, hvalue, htarget, htransfer,
      hentryStor, hentryBalance, hcallPostState⟩⟩

/-- The settled prefix and the accepted child entry meet at the exact paid
boundary of one withdrawal accounting step. -/
theorem WithdrawPreCallEffect.accountingEffect_of_acceptedPayout
    {sevm : Sevm} {pre callPre callPost guardPost returnPre : Devm}
    {paid : B256}
    (effect : WithdrawPreCallEffect sevm pre callPre)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget))
    (paid_eq : paid = Sevm.argWord sevm 0 *
      (Devm.getBal pre sevm.currentTarget + 1) /
        ((Devm.getStor pre sevm.currentTarget).get supplySlot + offset))
    (payout : AcceptedPayout sevm paid callPre callPost guardPost returnPre)
    (recipient_ne : sevm.caller.toB256.toAdr ≠ sevm.currentTarget) :
    ∃ trace : AcceptedPayoutTrace sevm paid callPre callPost,
      ProrataAccountingEffect offset.toNat
        (AccountingSnapshot.ofState sevm.currentTarget pre.state)
        (.withdraw (Sevm.argWord sevm 0).toNat paid.toNat)
        (AccountingSnapshot.ofState sevm.currentTarget trace.entry.state) := by
  obtain ⟨trace⟩ := payout.exists_trace recipient_ne
  have fields := effect
  unfold WithdrawPreCallEffect at fields
  dsimp at fields
  rcases fields with ⟨_, _, _, hcallBalance, _, _, _, _, _⟩
  have hcallBalanceAt :
      callPre.state.bal sevm.currentTarget =
        pre.state.bal sevm.currentTarget := by
    exact congrFun hcallBalance sevm.currentTarget
  have hpaidBalance :
      trace.entry.state.bal sevm.currentTarget =
        Devm.getBal pre sevm.currentTarget -
          (Sevm.argWord sevm 0 *
            (Devm.getBal pre sevm.currentTarget + 1) /
              ((Devm.getStor pre sevm.currentTarget).get supplySlot +
                offset)) := by
    rw [trace.entryBalance, hcallBalanceAt, paid_eq]
    rfl
  refine ⟨trace, ?_⟩
  simpa only [← paid_eq] using
    effect.accountingEffect invariant trace.entryStor hpaidBalance

/-- The realized accounting content of one successful deployed withdrawal.
Its first step stops at the paid child entry; the retained child trace then
runs to a state whose accounting projection is exactly the outer frame post. -/
structure RealizedWithdrawal (sevm : Sevm) (pre post : Devm) where
  paid : B256
  callPre : Devm
  callPost : Devm
  payout : AcceptedPayoutTrace sevm paid callPre callPost
  accounting : ProrataAccountingEffect offset.toNat
    (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
    (.withdraw (Sevm.argWord sevm 0).toNat paid.toNat)
    (AccountingSnapshot.ofState sevm.currentTarget payout.entry.state)
  postStor : Devm.getStor post = Devm.getStor callPost
  postBalance : Devm.getBal post = Devm.getBal callPost

/-- A successful withdrawal body realizes the exact paid-entry accounting
step and retains the callback trace needed to continue the replay. -/
theorem BodyEntry.realizedWithdrawal
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post Prorata.withdraw)
    (hvalue : sevm.value = 0)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget))
    (recipient_ne : sevm.caller.toB256.toAdr ≠ sevm.currentTarget) :
    Nonempty (RealizedWithdrawal sevm pre post) := by
  rcases entry with ⟨bodyPre, hstor, hbal, _, run⟩
  have bodyInvariant :
      Inv (Devm.getStor bodyPre sevm.currentTarget) sevm.value
        (Devm.getBal bodyPre sevm.currentTarget) := by
    rw [hstor, hbal]
    exact invariant
  let paid := Sevm.argWord sevm 0 *
    (Devm.getBal bodyPre sevm.currentTarget + 1) /
      ((Devm.getStor bodyPre sevm.currentTarget).get supplySlot + offset)
  have pays := withdraw_pays_exactly run
  change ∃ callPre callPost guardPost returnPre,
    WithdrawPreCallEffect sevm bodyPre callPre ∧
    AcceptedPayout sevm paid callPre callPost guardPost returnPre ∧
    Devm.getStor post = Devm.getStor callPost ∧
    Devm.getBal post = Devm.getBal callPost ∧
    ReturnsWord paid post at pays
  rcases pays with
    ⟨callPre, callPost, guardPost, returnPre, effect, payout,
      hpostStor, hpostBalance, _⟩
  rcases effect.accountingEffect_of_acceptedPayout bodyInvariant rfl payout
      recipient_ne with ⟨trace, accounting⟩
  have hpreSnapshot :
      AccountingSnapshot.ofState sevm.currentTarget bodyPre.state =
        AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state := by
    unfold AccountingSnapshot.ofState AccountingSnapshot.beforeCredit
    exact congrArg₂ AccountingSnapshot.mk
      (congrArg supplyN (congrFun hstor sevm.currentTarget))
      (by
        rw [hvalue]
        change (bodyPre.state.bal sevm.currentTarget).toNat =
          (pre.state.bal sevm.currentTarget).toNat - 0
        rw [Nat.sub_zero]
        exact congrArg B256.toNat (congrFun hbal sevm.currentTarget))
  have accounting' : ProrataAccountingEffect offset.toNat
      (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      (.withdraw (Sevm.argWord sevm 0).toNat paid.toNat)
      (AccountingSnapshot.ofState sevm.currentTarget trace.entry.state) := by
    rw [← hpreSnapshot]
    exact accounting
  refine ⟨{
    paid := paid
    callPre := callPre
    callPost := callPost
    payout := trace
    accounting := ?_
    postStor := hpostStor
    postBalance := hpostBalance }⟩
  · exact accounting'

/-- A positive world-state credit that leaves PRORATA storage fixed is the
frozen external-credit accounting class. -/
theorem accountingEffect_externalCredit
    {ca : Adr} {pre post : State} {amount : Nat}
    (hstor : post.getStor ca = pre.getStor ca)
    (hbalance : (post.bal ca).toNat = (pre.bal ca).toNat + amount)
    (hpositive : 0 < amount) :
    ProrataAccountingEffect offset.toNat
      (AccountingSnapshot.ofState ca pre) (.externalCredit amount)
      (AccountingSnapshot.ofState ca post) := by
  unfold AccountingSnapshot.ofState
  rw [hstor, hbalance]
  exact .externalCredit _ _ _ hpositive

/-- A boundary preserving the target storage and balance is exactly silent in
the four-way accounting vocabulary. -/
theorem accountingEffect_silent
    {ca : Adr} {pre post : State}
    (hstor : post.getStor ca = pre.getStor ca)
    (hbalance : post.bal ca = pre.bal ca) :
    ProrataAccountingEffect offset.toNat
      (AccountingSnapshot.ofState ca pre) .silent
      (AccountingSnapshot.ofState ca post) := by
  unfold AccountingSnapshot.ofState
  rw [hstor, hbalance]
  exact .silent _

/-- A nonpayable observation with unchanged target state is silent from its
semantic (pre-credit) entry as well. -/
theorem accountingEffect_silentBeforeCredit
    {sevm : Sevm} {pre post : Devm}
    (hvalue : sevm.value = 0)
    (hstor : Devm.getStor post sevm.currentTarget =
      Devm.getStor pre sevm.currentTarget)
    (hbalance : Devm.getBal post sevm.currentTarget =
      Devm.getBal pre sevm.currentTarget) :
    ProrataAccountingEffect offset.toNat
      (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      .silent (AccountingSnapshot.ofState sevm.currentTarget post.state) := by
  rw [show AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
      pre.state = AccountingSnapshot.ofState sevm.currentTarget pre.state
    from by
      unfold AccountingSnapshot.beforeCredit AccountingSnapshot.ofState
      rw [hvalue]
      rfl]
  exact accountingEffect_silent hstor hbalance

/-- The successful donation body changes neither persistent storage nor any
world balance; its only economic effect is the already-completed entry
credit. -/
theorem BodyEntry.donatePersistentEq
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post donate) :
    Devm.getStor post = Devm.getStor pre ∧
      Devm.getBal post = Devm.getBal pre := by
  rcases entry with ⟨bodyPre, hstor, hbal, -, run⟩
  have hstorBody : Devm.getStor bodyPre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold donate
      func_inv) run
  have hbalBody : Devm.getBal bodyPre = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal (by
      unfold donate
      func_inv) run
  exact ⟨hstorBody.symm.trans hstor, hbalBody.symm.trans hbal⟩

/-- A donation is either the positive external-credit class or, at zero
value, the silent class. -/
theorem BodyEntry.donateAccountingEffect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post donate)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget)) :
    ∃ kind,
      ProrataAccountingEffect offset.toNat
        (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state)
        kind (AccountingSnapshot.ofState sevm.currentTarget post.state) := by
  rcases entry.donatePersistentEq with ⟨hstor, hbal⟩
  let supply := supplyN (Devm.getStor pre sevm.currentTarget)
  let balance := (Devm.getBal pre sevm.currentTarget).toNat
  let amount := sevm.value.toNat
  have hpostSnapshot :
      AccountingSnapshot.ofState sevm.currentTarget post.state =
        ⟨supply, balance⟩ := by
    unfold AccountingSnapshot.ofState
    exact congrArg₂ AccountingSnapshot.mk
      (by
        change supplyN (Devm.getStor post sevm.currentTarget) = supply
        rw [congrFun hstor sevm.currentTarget])
      (by
        change (Devm.getBal post sevm.currentTarget).toNat = balance
        rw [congrFun hbal sevm.currentTarget])
  have hcredited : balance - amount + amount = balance :=
    Nat.sub_add_cancel invariant.value_le_balance
  by_cases hpositive : 0 < amount
  · refine ⟨.externalCredit amount, ?_⟩
    rw [show AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
        pre.state = ⟨supply, balance - amount⟩ from rfl, hpostSnapshot]
    simpa only [hcredited] using
      (ProrataAccountingEffect.externalCredit
        supply (balance - amount) amount hpositive)
  · have hzero : amount = 0 := Nat.eq_zero_of_not_pos hpositive
    refine ⟨.silent, ?_⟩
    rw [show AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
        pre.state = ⟨supply, balance - amount⟩ from rfl, hpostSnapshot,
      hzero]
    exact .silent _

/-- The successful shares preview is a silent accounting observation. -/
theorem BodyEntry.sharesAccountingEffect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post convertToShares)
    (hvalue : sevm.value = 0) :
    ProrataAccountingEffect offset.toNat
      (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      .silent (AccountingSnapshot.ofState sevm.currentTarget post.state) := by
  rcases entry with ⟨bodyPre, hstor, hbal, -, run⟩
  have effect := convertToShares_effect run
  unfold SharesViewEffect at effect
  dsimp at effect
  rcases effect with ⟨-, -, -, -, hpostStor, hpostBal, -, -⟩
  exact accountingEffect_silentBeforeCredit hvalue
    (congrFun (hpostStor.trans hstor) sevm.currentTarget)
    (congrFun (hpostBal.trans hbal) sevm.currentTarget)

/-- The successful assets preview is a silent accounting observation. -/
theorem BodyEntry.assetsAccountingEffect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post convertToAssets)
    (hvalue : sevm.value = 0) :
    ProrataAccountingEffect offset.toNat
      (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      .silent (AccountingSnapshot.ofState sevm.currentTarget post.state) := by
  rcases entry with ⟨bodyPre, hstor, hbal, -, run⟩
  have effect := convertToAssets_effect run
  unfold AssetsViewEffect at effect
  dsimp at effect
  rcases effect with ⟨-, -, -, hpostStor, hpostBal, -, -⟩
  exact accountingEffect_silentBeforeCredit hvalue
    (congrFun (hpostStor.trans hstor) sevm.currentTarget)
    (congrFun (hpostBal.trans hbal) sevm.currentTarget)

/-- A list presentation of connected accounting effects, retaining its exact
initial and terminal snapshots while remaining convenient for induction. -/
inductive ProrataAccountingReplay (o : Nat) :
    AccountingSnapshot → List (ProrataAccountingStep o) →
      AccountingSnapshot → Prop where
  | nil (snapshot : AccountingSnapshot) :
      ProrataAccountingReplay o snapshot [] snapshot
  | cons {step : ProrataAccountingStep o}
      {steps : List (ProrataAccountingStep o)} {post : AccountingSnapshot}
      (tail : ProrataAccountingReplay o step.post steps post) :
      ProrataAccountingReplay o step.pre (step :: steps) post

namespace ProrataAccountingReplay

/-- One realized effect is a connected singleton replay. -/
theorem singleton {o : Nat} {pre post : AccountingSnapshot}
    {kind : ProrataAccountingKind}
    (provenance : ProrataAccountingProvenance)
    (effect : ProrataAccountingEffect o pre kind post) :
    ProrataAccountingReplay o pre
      [{ pre, post, kind, provenance, effect }] post := by
  exact ProrataAccountingReplay.cons
    (step := { pre, post, kind, provenance, effect })
    (ProrataAccountingReplay.nil post)

/-- Concatenate two accounting replays at their shared boundary. -/
theorem append {o : Nat} {pre mid post : AccountingSnapshot}
    {left right : List (ProrataAccountingStep o)}
    (before : ProrataAccountingReplay o pre left mid)
    (after : ProrataAccountingReplay o mid right post) :
    ProrataAccountingReplay o pre (left ++ right) post := by
  induction before with
  | nil snapshot =>
      simpa using after
  | cons tail ih =>
      simpa using ProrataAccountingReplay.cons (ih after)

/-- Equal projected boundaries contribute no accounting step. -/
theorem nil_of_eq {o : Nat} {pre post : AccountingSnapshot}
    (eq : post = pre) : ProrataAccountingReplay o pre [] post := by
  rw [eq]
  exact .nil pre

/-- A successful transfer from an address other than PRORATA either credits
PRORATA exactly or leaves its accounting projection unchanged. -/
theorem of_transfer_from_ne
    {ca caller target : Adr} {pre debit : State} {value : B256}
    (provenance : ProrataAccountingProvenance)
    (caller_ne : caller ≠ ca)
    (sub : pre.subBal caller value = some debit)
    (sum_nof : sum pre.bal < 2 ^ 256) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca pre) steps
        (AccountingSnapshot.ofState ca (debit.addBal target value)) := by
  have fields := of_state_transfer_fields (callee := target) sub
  by_cases target_eq : target = ca
  · subst target
    have balance_eq :
        ((debit.addBal ca value).bal ca).toNat =
          (pre.bal ca).toNat + value.toNat :=
      of_transfer_bal_target sub caller_ne sum_nof
    by_cases positive : 0 < value.toNat
    · exact ⟨_, singleton provenance
        (accountingEffect_externalCredit (fields.1 ca) balance_eq positive)⟩
    · have zero : value.toNat = 0 := Nat.eq_zero_of_not_pos positive
      have snapshot_eq :
          AccountingSnapshot.ofState ca (debit.addBal ca value) =
            AccountingSnapshot.ofState ca pre := by
        unfold AccountingSnapshot.ofState
        exact congrArg₂ AccountingSnapshot.mk
          (congrArg supplyN (fields.1 ca))
          (by rw [balance_eq, zero, Nat.add_zero])
      exact ⟨[], nil_of_eq snapshot_eq⟩
  · have balance_eq :
        (debit.addBal target value).bal ca = pre.bal ca :=
      of_transfer_bal_other sub caller_ne target_eq
    have snapshot_eq :
        AccountingSnapshot.ofState ca (debit.addBal target value) =
          AccountingSnapshot.ofState ca pre := by
      unfold AccountingSnapshot.ofState
      exact congrArg₂ AccountingSnapshot.mk
        (congrArg supplyN (fields.1 ca))
        (congrArg B256.toNat balance_eq)
    exact ⟨[], nil_of_eq snapshot_eq⟩

/-- A direct world-state balance credit is an exact external-credit step when
it targets PRORATA and is positive; every other case is a projected no-op. -/
theorem of_addBal
    {ca target : Adr} {pre : State} {value : B256}
    (provenance : ProrataAccountingProvenance)
    (sum_nof : sum pre.bal + value.toNat < 2 ^ 256) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca pre) steps
        (AccountingSnapshot.ofState ca (pre.addBal target value)) := by
  have storage_eq :
      (pre.addBal target value).getStor ca = pre.getStor ca := by
    show ((pre.setBal target (pre.bal target + value)).get ca).stor =
      (pre.get ca).stor
    rw [State.setBal_get_stor]
  by_cases target_eq : target = ca
  · subst target
    have nof : B256.Nof (pre.bal ca) value := by
      unfold B256.Nof
      have target_le : (pre.bal ca).toNat ≤ sum pre.bal := le_sum
      omega
    have balance_eq :
        ((pre.addBal ca value).bal ca).toNat =
          (pre.bal ca).toNat + value.toNat := by
      have word_eq : (pre.addBal ca value).bal ca =
          pre.bal ca + value := by
        show ((pre.setBal ca (pre.bal ca + value)).get ca).bal = _
        rw [State.setBal_get_self]
        rfl
      rw [word_eq, B256.toNat_add_eq_of_nof _ _ nof]
    by_cases positive : 0 < value.toNat
    · exact ⟨_, singleton provenance
        (accountingEffect_externalCredit storage_eq balance_eq positive)⟩
    · have zero : value.toNat = 0 := Nat.eq_zero_of_not_pos positive
      have snapshot_eq :
          AccountingSnapshot.ofState ca (pre.addBal ca value) =
            AccountingSnapshot.ofState ca pre := by
        unfold AccountingSnapshot.ofState
        exact congrArg₂ AccountingSnapshot.mk
          (congrArg supplyN storage_eq)
          (by rw [balance_eq, zero, Nat.add_zero])
      exact ⟨[], nil_of_eq snapshot_eq⟩
  · have balance_eq : (pre.addBal target value).bal ca = pre.bal ca := by
      show ((pre.setBal target (pre.bal target + value)).get ca).bal = _
      rw [State.setBal_get_ne target_eq]
      rfl
    have snapshot_eq :
        AccountingSnapshot.ofState ca (pre.addBal target value) =
          AccountingSnapshot.ofState ca pre := by
      unfold AccountingSnapshot.ofState
      exact congrArg₂ AccountingSnapshot.mk
        (congrArg supplyN storage_eq)
        (congrArg B256.toNat balance_eq)
    exact ⟨[], nil_of_eq snapshot_eq⟩

/-- Every replay yields the frozen connected-path carrier used by the exact
dust theorem; no boundary connectivity is reconstructed axiomatically. -/
theorem exists_path {o : Nat} {pre post : AccountingSnapshot}
    {steps : List (ProrataAccountingStep o)}
    (replay : ProrataAccountingReplay o pre steps post) :
    ∃ path : ProrataAccountingPath o,
      path.steps = steps ∧ path.first = pre ∧ path.last = post := by
  induction replay with
  | nil snapshot =>
      exact ⟨ProrataAccountingPath.nil o snapshot, rfl, rfl, rfl⟩
  | @cons step steps post tail ih =>
      rcases ih with ⟨path, hsteps, hfirst, hlast⟩
      have connect : step.post = path.first := hfirst.symm
      refine ⟨ProrataAccountingPath.cons step path connect, ?_, ?_, ?_⟩
      · rw [ProrataAccountingPath.cons]
        simp only
        rw [hsteps]
      · rfl
      · simpa using hlast

end ProrataAccountingReplay

/-- Every successful deployed route except withdrawal is already a complete
singleton accounting replay.  The withdrawal arm is retained for the
settlement-aware child recursion that follows. -/
theorem ProrataMainRoute.accountingReplay_or_withdraw
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (route : ProrataMainRoute fs sevm pre post)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget))
    (provenance : ProrataAccountingProvenance) :
    (∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state)
        steps (AccountingSnapshot.ofState sevm.currentTarget post.state)) ∨
      Nonempty (BodyEntry fs sevm pre post Prorata.withdraw) ∧
        sevm.value = 0 := by
  cases route with
  | deposit entry =>
      rcases entry.depositAccountingEffect invariant with ⟨minted, effect⟩
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance effect⟩
  | withdraw hvalue entry =>
      exact Or.inr ⟨⟨entry⟩, hvalue⟩
  | convertToShares hvalue entry =>
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance
          (entry.sharesAccountingEffect hvalue)⟩
  | convertToAssets hvalue entry =>
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance
          (entry.assetsAccountingEffect hvalue)⟩
  | donate entry =>
      rcases entry.donateAccountingEffect invariant with ⟨kind, effect⟩
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance effect⟩

/-- An exact retained PRORATA frame is either already a complete replay or is
the unique withdrawal shape whose paid child trace must be replayed next. -/
theorem Exec.Frame.accountingReplay_or_realizedWithdrawal
    {ca : Adr} {frame : Exec.Frame}
    (invocation : frame.exactInvocation prorata ca ca)
    (precondition : prorataSpec.Pre ca frame.sevm frame.pre)
    (provenance : ProrataAccountingProvenance)
    (recipient_ne : frame.sevm.caller.toB256.toAdr ≠ ca) :
    (∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.beforeCredit ca frame.sevm.value frame.pre.state)
        steps (AccountingSnapshot.ofState ca frame.post.state)) ∨
      Nonempty (RealizedWithdrawal frame.sevm frame.pre frame.post) := by
  have target_eq : frame.sevm.currentTarget = ca := invocation.2.1
  have preInvariant := precondition.inv
  unfold ContractSpec.PreInv at preInvariant
  have invariantCa :
      Inv (Devm.getStor frame.pre ca) frame.sevm.value
        (Devm.getBal frame.pre ca) :=
    preInvariant.1 target_eq
  have invariant :
      Inv (Devm.getStor frame.pre frame.sevm.currentTarget) frame.sevm.value
        (Devm.getBal frame.pre frame.sevm.currentTarget) := by
    rw [target_eq]
    exact invariantCa
  have route := exactInvocation_route invocation
  rcases route.accountingReplay_or_withdraw invariant provenance with
      replay | ⟨⟨entry⟩, hvalue⟩
  · left
    simpa only [target_eq] using replay
  · right
    have recipient_ne' :
        frame.sevm.caller.toB256.toAdr ≠ frame.sevm.currentTarget := by
      simpa only [target_eq] using recipient_ne
    exact entry.realizedWithdrawal hvalue invariant recipient_ne'

end Prorata

end Blanc
