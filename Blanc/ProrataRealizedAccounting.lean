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
    ∃ paid,
      ProrataAccountingEffect offset.toNat
        (AccountingSnapshot.ofState sevm.currentTarget pre.state)
        (.withdraw (Sevm.argWord sevm 0).toNat paid)
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
  refine ⟨paid.toNat, ?_⟩
  rw [show AccountingSnapshot.ofState sevm.currentTarget pre.state =
      ⟨supplyN stor, balance.toNat⟩ from rfl]
  rw [show AccountingSnapshot.ofState sevm.currentTarget paidState =
      ⟨supplyN stor - shares.toNat, balance.toNat - paid.toNat⟩ from by
      exact congrArg₂ AccountingSnapshot.mk hpostSupply hpostBalance]
  exact .withdraw _ _ _ _
    (B256.toNat_le_toNat hsharesSupply) hquote

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

end Prorata

end Blanc
