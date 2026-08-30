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
def ofWorldState (ca : Adr) (state : State) : AccountingSnapshot :=
  ⟨supplyN (state.getStor ca), (state.bal ca).toNat⟩

end AccountingSnapshot

/-- The realized PRORATA accounting boundary.

The frozen `AccountingSnapshot` records only the two Nat quantities the
cumulative-dust identity prices with, so a step recorded over it cannot say
*whose* shares moved.  A realized boundary keeps PRORATA's own persistent
storage in place of the total that summarizes it, so the caller-keyed share
ledger survives the boundary; the ETH balance stays a `Nat` because a semantic
boundary may sit immediately before an already-credited call value, which is
not any world state's balance.

`snapshot` is the frozen projection, so everything stated over snapshots reads
unchanged one level down. -/
structure RealizedSnapshot where
  stor : Stor
  balance : Nat

namespace RealizedSnapshot

/-- The frozen accounting projection of a realized boundary. -/
def snapshot (boundary : RealizedSnapshot) : AccountingSnapshot :=
  ⟨supplyN boundary.stor, boundary.balance⟩

/-- The caller-keyed share ledger of a realized boundary: the address-shaped
storage rows, which are exactly the domain `balSum` sums over. -/
def ledger (boundary : RealizedSnapshot) : Adr → B256 :=
  Stor.rest boundary.stor

/-- The realized PRORATA boundary of one exact world state. -/
def ofState (ca : Adr) (state : State) : RealizedSnapshot :=
  ⟨state.getStor ca, (state.bal ca).toNat⟩

/-- The semantic pre-credit boundary at an entered value-carrying message. -/
def beforeCredit (ca : Adr) (value : B256) (state : State) :
    RealizedSnapshot :=
  ⟨state.getStor ca, (state.bal ca).toNat - value.toNat⟩

/-- The realized boundary at message entry.  A message entering PRORATA is
viewed immediately before its value credit; every foreign message is viewed
at its ordinary world-state projection. -/
def messageEntry (ca : Adr) (msg : Msg) (state : State) :
    RealizedSnapshot :=
  if msg.currentTarget = ca then beforeCredit ca msg.value state
  else ofState ca state

/-- The realized boundary projects onto the frozen accounting snapshot. -/
@[simp] theorem snapshot_ofState (ca : Adr) (state : State) :
    (ofState ca state).snapshot = AccountingSnapshot.ofWorldState ca state := rfl

theorem ofState_snapshot (ca : Adr) (state : State) :
    (ofState ca state).snapshot =
      ⟨supplyN (state.getStor ca), (state.bal ca).toNat⟩ := rfl

theorem ofState_ledger (ca : Adr) (state : State) :
    (ofState ca state).ledger = Stor.rest (state.getStor ca) := rfl

theorem beforeCredit_snapshot (ca : Adr) (value : B256) (state : State) :
    (beforeCredit ca value state).snapshot =
      ⟨supplyN (state.getStor ca), (state.bal ca).toNat - value.toNat⟩ := rfl

theorem beforeCredit_ledger (ca : Adr) (value : B256) (state : State) :
    (beforeCredit ca value state).ledger = Stor.rest (state.getStor ca) := rfl

/-- Equal PRORATA storage and balance is equal realized boundary.  This is the
shape almost every projected no-op boundary equality takes. -/
theorem ofState_congr {ca : Adr} {pre post : State}
    (hstor : post.getStor ca = pre.getStor ca)
    (hbal : post.bal ca = pre.bal ca) :
    ofState ca post = ofState ca pre :=
  congrArg₂ RealizedSnapshot.mk hstor (congrArg B256.toNat hbal)

/-- A successful EVM message transfer connects its semantic entry boundary
exactly to the ordinary realized boundary of the pre-transfer state. -/
theorem messageEntry_eq_ofState
    {ca : Adr} {msg : Msg} {entry : Benv}
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256) :
    messageEntry ca msg entry.state = ofState ca msg.benv.state := by
  cases shouldTransfer : msg.shouldTransferValue with
  | false =>
      have noTransfer : ¬ msg.shouldTransferValue = true := by
        simp [shouldTransfer]
      have entry_eq := of_benvAfterTransfer_no noTransfer transfer
      subst entry
      by_cases target_eq : msg.currentTarget = ca
      · have valueNat : msg.value.toNat = 0 := by
          rw [value_zero shouldTransfer target_eq]
          rfl
        simp [messageEntry, target_eq, beforeCredit, ofState, valueNat]
      · simp [messageEntry, target_eq]
  | true =>
      rcases of_benvAfterTransfer shouldTransfer transfer with
        ⟨debit, sub, rfl⟩
      have fields := of_state_transfer_fields
        (callee := msg.currentTarget) sub
      by_cases target_eq : msg.currentTarget = ca
      · subst ca
        unfold messageEntry
        rw [if_pos rfl]
        unfold beforeCredit ofState
        apply congrArg₂ RealizedSnapshot.mk
        · exact fields.1 msg.currentTarget
        · change ((debit.addBal msg.currentTarget msg.value).bal
              msg.currentTarget).toNat - msg.value.toNat = _
          rw [of_transfer_bal_target sub (caller_ne shouldTransfer) sum_nof]
          exact Nat.add_sub_cancel _ _
      · unfold messageEntry
        rw [if_neg target_eq]
        unfold ofState
        apply congrArg₂ RealizedSnapshot.mk
        · exact fields.1 ca
        · exact congrArg B256.toNat
            (of_transfer_bal_other sub (caller_ne shouldTransfer) target_eq)

end RealizedSnapshot

/-- The exact share-ledger movement of one classified accounting step.

The frozen four-way classification prices a step but never names a holder, so
by itself it admits a withdrawal that burns someone else's shares.  This is
the missing half, and the whole reason the realized carrier keeps storage: a
priced step moves exactly its own actor's ledger row, by exactly its own share
amount, and leaves every other row alone; an unpriced step moves no row at
all.  A withdrawal additionally covers its burn from the actor's own row,
which is what makes a burn impossible to aim at another holder. -/
def LedgerMove : ProrataAccountingKind → Option Adr →
    (Adr → B256) → (Adr → B256) → Prop
  | .deposit _ minted, actor, pre, post =>
      ∃ x : Adr, actor = some x ∧
        (post x).toNat = (pre x).toNat + minted ∧
        ∀ b : Adr, b ≠ x → post b = pre b
  | .withdraw shares _, actor, pre, post =>
      ∃ x : Adr, actor = some x ∧
        shares ≤ (pre x).toNat ∧
        (post x).toNat = (pre x).toNat - shares ∧
        ∀ b : Adr, b ≠ x → post b = pre b
  | .externalCredit _, _, pre, post => post = pre
  | .silent, _, pre, post => post = pre

/-- A ledger movement is read at whatever actor the chronology records, so a
step built from a leaf lemma (which knows the caller) transfers to a step
built from retained provenance (which records it). -/
theorem LedgerMove.of_actor_eq {kind : ProrataAccountingKind}
    {actor actor' : Option Adr} {pre post : Adr → B256}
    (move : LedgerMove kind actor pre post) (eq : actor' = actor) :
    LedgerMove kind actor' pre post := by
  rw [eq]; exact move

/-- No step moves the share row of anyone but its own recorded actor.

This is the fact the actor overlay is blocked on, and it holds uniformly
across all four classes: an attacker's withdrawal cannot burn another
holder's shares, and a step with no recorded actor moves no row at all. -/
theorem LedgerMove.eq_of_ne_actor {kind : ProrataAccountingKind}
    {actor : Option Adr} {pre post : Adr → B256} {y : Adr}
    (move : LedgerMove kind actor pre post) (ne : actor ≠ some y) :
    post y = pre y := by
  cases kind with
  | deposit amount minted =>
      obtain ⟨x, hactor, -, hother⟩ := move
      exact hother y fun hy => ne (hactor.trans (congrArg some hy.symm))
  | withdraw shares paid =>
      obtain ⟨x, hactor, -, -, hother⟩ := move
      exact hother y fun hy => ne (hactor.trans (congrArg some hy.symm))
  | externalCredit amount => exact congrFun move y
  | silent => exact congrFun move y

/-- A deposit credits exactly the depositing actor's own ledger row. -/
theorem LedgerMove.deposit_row {amount minted : Nat} {actor : Option Adr}
    {pre post : Adr → B256} {x : Adr}
    (move : LedgerMove (.deposit amount minted) actor pre post)
    (hactor : actor = some x) :
    (post x).toNat = (pre x).toNat + minted := by
  obtain ⟨x', hx, hrow, -⟩ := move
  obtain rfl := Option.some.inj (hactor.symm.trans hx)
  exact hrow

/-- A withdrawal covers its burn from the withdrawing actor's own row. -/
theorem LedgerMove.withdraw_cover {shares paid : Nat} {actor : Option Adr}
    {pre post : Adr → B256} {x : Adr}
    (move : LedgerMove (.withdraw shares paid) actor pre post)
    (hactor : actor = some x) : shares ≤ (pre x).toNat := by
  obtain ⟨x', hx, hle, -, -⟩ := move
  obtain rfl := Option.some.inj (hactor.symm.trans hx)
  exact hle

/-- A withdrawal debits exactly the withdrawing actor's own ledger row. -/
theorem LedgerMove.withdraw_row {shares paid : Nat} {actor : Option Adr}
    {pre post : Adr → B256} {x : Adr}
    (move : LedgerMove (.withdraw shares paid) actor pre post)
    (hactor : actor = some x) :
    (post x).toNat = (pre x).toNat - shares := by
  obtain ⟨x', hx, -, hrow, -⟩ := move
  obtain rfl := Option.some.inj (hactor.symm.trans hx)
  exact hrow

/-- One realized accounting step: the frozen classification of the boundary
together with the exact ledger movement that produced it. -/
structure RealizedEffect (o : Nat) (kind : ProrataAccountingKind)
    (actor : Option Adr) (pre post : RealizedSnapshot) : Prop where
  effect : ProrataAccountingEffect o pre.snapshot kind post.snapshot
  ledger : LedgerMove kind actor pre.ledger post.ledger

/-- PRORATA's mint write, read on the share ledger.  The supply write is
invisible here (the supply slot is not address-shaped), so the caller's own
row rises by exactly the minted shares and no other row moves. -/
theorem ledger_mint (s : Stor) (a : Adr) (v m : B256)
    (nof : B256.Nof (s.get a.toB256) m) :
    (Stor.rest ((s.set supplySlot v).set a.toB256 (s.get a.toB256 + m)) a).toNat =
        (Stor.rest s a).toNat + m.toNat ∧
      ∀ b : Adr, b ≠ a →
        Stor.rest ((s.set supplySlot v).set a.toB256 (s.get a.toB256 + m)) b =
          Stor.rest s b := by
  constructor
  · rw [Stor.rest_set_self, B256.toNat_add_eq_of_nof _ _ nof]
    rfl
  · intro b hb
    rw [Stor.rest_set_ne _ hb, Stor.rest_set_prorataSupplySlot]

/-- PRORATA's burn write, read on the share ledger: the caller's own row falls
by exactly the burned shares and no other row moves. -/
theorem ledger_burn (s : Stor) (a : Adr) (v m : B256)
    (le : m ≤ s.get a.toB256) :
    (Stor.rest ((s.set a.toB256 (s.get a.toB256 - m)).set supplySlot v) a).toNat =
        (Stor.rest s a).toNat - m.toNat ∧
      ∀ b : Adr, b ≠ a →
        Stor.rest ((s.set a.toB256 (s.get a.toB256 - m)).set supplySlot v) b =
          Stor.rest s b := by
  constructor
  · rw [Stor.rest_set_prorataSupplySlot, Stor.rest_set_self,
      B256.toNat_sub_eq_of_le _ _ le]
    rfl
  · intro b hb
    rw [Stor.rest_set_prorataSupplySlot, Stor.rest_set_ne _ hb]

/-- Retag a realized step with an equal recorded actor. -/
theorem RealizedEffect.of_actor_eq {o : Nat} {kind : ProrataAccountingKind}
    {actor actor' : Option Adr} {pre post : RealizedSnapshot}
    (realized : RealizedEffect o kind actor pre post) (eq : actor' = actor) :
    RealizedEffect o kind actor' pre post :=
  ⟨realized.effect, realized.ledger.of_actor_eq eq⟩

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
      RealizedEffect offset.toNat (.deposit sevm.value.toNat minted)
        (some sevm.caller)
        (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
        (RealizedSnapshot.ofState sevm.currentTarget post.state) := by
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
  have hcallerNof : B256.Nof (stor.get sevm.caller.toB256) minted := by
    have hle : (stor.get sevm.caller.toB256).toNat ≤ supply.toNat :=
      B256.toNat_le_toNat (invariant.share_word_le_supply sevm.caller)
    unfold B256.Nof at hmintNof ⊢
    omega
  refine ⟨minted.toNat, ?_, ?_⟩
  · show ProrataAccountingEffect offset.toNat
      ⟨supplyN stor, balance.toNat - sevm.value.toNat⟩ _ _
    rw [show (RealizedSnapshot.ofState sevm.currentTarget post.state).snapshot =
        ⟨supplyN stor + minted.toNat,
          (balance.toNat - sevm.value.toNat) + sevm.value.toNat⟩ from by
        exact congrArg₂ AccountingSnapshot.mk hpostSupply hpostBalance]
    exact .deposit _ _ _ _ hquote
  · refine ⟨sevm.caller, rfl, ?_⟩
    rw [show (RealizedSnapshot.ofState sevm.currentTarget post.state).ledger =
        Stor.rest (Devm.getStor post sevm.currentTarget) from rfl, hstor]
    exact ledger_mint stor sevm.caller (supply + minted) minted hcallerNof

/-- The deposit accounting effect survives the dispatcher's persistent-state
silent walk from retained frame entry to the raw source body. -/
theorem BodyEntry.depositAccountingEffect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post deposit)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget)) :
    ∃ minted,
      RealizedEffect offset.toNat (.deposit sevm.value.toNat minted)
        (some sevm.caller)
        (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
        (RealizedSnapshot.ofState sevm.currentTarget post.state) := by
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
      RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
          bodyPre.state =
        RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state := by
    unfold RealizedSnapshot.beforeCredit
    exact congrArg₂ RealizedSnapshot.mk
      (congrFun hstor sevm.currentTarget)
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
    RealizedEffect offset.toNat
      (.withdraw (Sevm.argWord sevm 0).toNat
        (Sevm.argWord sevm 0 *
          (Devm.getBal pre sevm.currentTarget + 1) /
            ((Devm.getStor pre sevm.currentTarget).get supplySlot + offset)).toNat)
      (some sevm.caller)
      (RealizedSnapshot.ofState sevm.currentTarget pre.state)
      (RealizedSnapshot.ofState sevm.currentTarget paidState) := by
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
  refine ⟨?_, ?_⟩
  · show ProrataAccountingEffect offset.toNat ⟨supplyN stor, balance.toNat⟩ _ _
    rw [show (RealizedSnapshot.ofState sevm.currentTarget paidState).snapshot =
        ⟨supplyN stor - shares.toNat, balance.toNat - paid.toNat⟩ from by
        exact congrArg₂ AccountingSnapshot.mk hpostSupply hpostBalance]
    exact .withdraw _ _ _ _
      (B256.toNat_le_toNat hsharesSupply) hquote
  · refine ⟨sevm.caller, rfl, B256.toNat_le_toNat hcover, ?_⟩
    rw [show (RealizedSnapshot.ofState sevm.currentTarget paidState).ledger =
        Stor.rest (paidState.getStor sevm.currentTarget) from rfl,
      hpaidStor, hstor]
    exact ledger_burn stor sevm.caller (supply - shares) shares hcover

/-- The exact child-message entry selected by an accepted withdrawal payout.
This packages the semantic paid boundary separately from the callback-final
state, together with the retained child trace needed for recursive replay. -/
structure AcceptedPayoutTrace
    (sevm : Sevm) (paid : B256) (callPre callPost : Devm) where
  childMsg : Msg
  entry : Benv
  child : Devm
  trace : ExecutionTrace.ProcessMessageTrace childMsg (.ok child)
  childClean : child.error.isSome = false
  messageState : childMsg.benv.state = callPre.state
  shouldTransferValue : childMsg.shouldTransferValue = true
  caller : childMsg.caller = sevm.currentTarget
  value : childMsg.value = paid
  target : childMsg.currentTarget = sevm.caller.toB256.toAdr
  targetNe : childMsg.currentTarget ≠ sevm.currentTarget
  depth : (initSevm (childMsg.withBenv entry)).depth < sevm.depth
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
  have htargetNe : childMsg.currentTarget ≠ sevm.currentTarget := by
    rw [htarget]
    exact recipient_ne
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
    have hchildDepth :
        (initSevm (childMsg.withBenv entry)).depth < sevm.depth := by
      change sevm.depth - 1 < sevm.depth
      omega
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
    exact ⟨⟨childMsg, entry, child, trace, hclean, hmessageState,
      hshouldTransfer, hcaller, hvalue, htarget, htargetNe, hchildDepth, htransfer,
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
      RealizedEffect offset.toNat
        (.withdraw (Sevm.argWord sevm 0).toNat paid.toNat)
        (some sevm.caller)
        (RealizedSnapshot.ofState sevm.currentTarget pre.state)
        (RealizedSnapshot.ofState sevm.currentTarget trace.entry.state) := by
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

/-- The accepted callback starts from the full PRORATA precondition at its
exact post-transfer entry state.  This is the recursive invariant handoff;
it does not summarize or assume anything about the callback's behavior. -/
theorem WithdrawPreCallEffect.acceptedPayoutChildPre
    {sevm : Sevm} {pre callPre callPost : Devm} {paid : B256}
    (effect : WithdrawPreCallEffect sevm pre callPre)
    (precondition : prorataSpec.Pre sevm.currentTarget sevm pre)
    (paid_eq : paid = Sevm.argWord sevm 0 *
      (Devm.getBal pre sevm.currentTarget + 1) /
        ((Devm.getStor pre sevm.currentTarget).get supplySlot + offset))
    (trace : AcceptedPayoutTrace sevm paid callPre callPost) :
    prorataSpec.Pre sevm.currentTarget
      (initSevm (trace.childMsg.withBenv trace.entry))
      (initDevm (trace.childMsg.withBenv trace.entry)) := by
  have preInvariant :
      Inv (Devm.getStor pre sevm.currentTarget) sevm.value
        (Devm.getBal pre sevm.currentTarget) :=
    precondition.inv.left rfl
  have effectFields := effect
  unfold WithdrawPreCallEffect at effectFields
  dsimp at effectFields
  rcases effectFields with
    ⟨_, _, _, callBalance, callCode, _, _, _, _⟩
  have childCode :
      some (callPre.getCode sevm.currentTarget).toList =
        Prog.compile prorataSpec.prog := by
    rw [callCode]
    exact precondition.code
  have childSide : prorataSpec.Side callPre.getBal := by
    rw [callBalance]
    exact precondition.side
  have childInvariant :
      Inv (Devm.getStor callPre sevm.currentTarget) 0
        (Devm.getBal callPre sevm.currentTarget - paid) := by
    rw [congrFun callBalance sevm.currentTarget, paid_eq]
    exact effect.settlement_inv preInvariant
  rcases of_benvAfterTransfer trace.shouldTransferValue trace.entryTransfer with
    ⟨debit, sub, entry_eq⟩
  rw [trace.messageState, trace.caller, trace.value] at sub
  have entryState : trace.entry.state =
      debit.addBal sevm.caller.toB256.toAdr paid := by
    rw [entry_eq, trace.target, trace.value]
    rfl
  apply ContractSpec.Pre.child_of_outbound_transfer
    (st := callPre.state) (st_mid := debit)
    (target := sevm.caller.toB256.toAdr) (value := paid)
  · exact childCode
  · exact childSide
  · exact childInvariant
  · exact sub
  · exact entryState
  · exact trace.target
  · exact trace.value

/-- The realized accounting content of one successful deployed withdrawal.
Its first step stops at the paid child entry; the retained child trace then
runs to a state whose accounting projection is exactly the outer frame post. -/
structure RealizedWithdrawal (sevm : Sevm) (pre post : Devm) where
  paid : B256
  callPre : Devm
  callPost : Devm
  payout : AcceptedPayoutTrace sevm paid callPre callPost
  childPre : prorataSpec.Pre sevm.currentTarget
    (initSevm (payout.childMsg.withBenv payout.entry))
    (initDevm (payout.childMsg.withBenv payout.entry))
  accounting : RealizedEffect offset.toNat
    (.withdraw (Sevm.argWord sevm 0).toNat paid.toNat)
    (some sevm.caller)
    (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
    (RealizedSnapshot.ofState sevm.currentTarget payout.entry.state)
  postStor : Devm.getStor post = Devm.getStor callPost
  postBalance : Devm.getBal post = Devm.getBal callPost

/-- The retained callback result is the exact accounting endpoint of the
outer withdrawal frame.  Machine-local return cleanup is erased here, while
the target storage and balance remain tied to the callback state. -/
theorem RealizedWithdrawal.postSnapshot
    {sevm : Sevm} {pre post : Devm}
    (withdrawal : RealizedWithdrawal sevm pre post) :
    RealizedSnapshot.ofState sevm.currentTarget post.state =
      RealizedSnapshot.ofState sevm.currentTarget
        withdrawal.payout.child.state := by
  have outerToCall :
      RealizedSnapshot.ofState sevm.currentTarget post.state =
        RealizedSnapshot.ofState sevm.currentTarget
          withdrawal.callPost.state := by
    unfold RealizedSnapshot.ofState
    exact congrArg₂ RealizedSnapshot.mk
      (congrFun withdrawal.postStor sevm.currentTarget)
      (congrArg B256.toNat
        (congrFun withdrawal.postBalance sevm.currentTarget))
  have callToChild :
      RealizedSnapshot.ofState sevm.currentTarget
          withdrawal.callPost.state =
        RealizedSnapshot.ofState sevm.currentTarget
          withdrawal.payout.child.state :=
    congrArg (RealizedSnapshot.ofState sevm.currentTarget)
      withdrawal.payout.callPostState
  exact outerToCall.trans callToChild

/-- A successful withdrawal body realizes the exact paid-entry accounting
step and retains the callback trace needed to continue the replay. -/
theorem BodyEntry.realizedWithdrawal
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post Prorata.withdraw)
    (hvalue : sevm.value = 0)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget))
    (precondition : prorataSpec.Pre sevm.currentTarget sevm pre)
    (recipient_ne : sevm.caller.toB256.toAdr ≠ sevm.currentTarget) :
    Nonempty (RealizedWithdrawal sevm pre post) := by
  rcases entry with ⟨bodyPre, hstor, hbal, hcode, run⟩
  have bodyInvariant :
      Inv (Devm.getStor bodyPre sevm.currentTarget) sevm.value
        (Devm.getBal bodyPre sevm.currentTarget) := by
    rw [hstor, hbal]
    exact invariant
  have bodyPrecondition :
      prorataSpec.Pre sevm.currentTarget sevm bodyPre :=
    ContractSpec.Pre.of_eqs precondition
      (congrFun hcode sevm.currentTarget) hbal
      (congrFun hstor sevm.currentTarget)
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
      RealizedSnapshot.ofState sevm.currentTarget bodyPre.state =
        RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state := by
    unfold RealizedSnapshot.ofState RealizedSnapshot.beforeCredit
    exact congrArg₂ RealizedSnapshot.mk
      (congrFun hstor sevm.currentTarget)
      (by
        rw [hvalue]
        change (bodyPre.state.bal sevm.currentTarget).toNat =
          (pre.state.bal sevm.currentTarget).toNat - 0
        rw [Nat.sub_zero]
        exact congrArg B256.toNat (congrFun hbal sevm.currentTarget))
  have accounting' : RealizedEffect offset.toNat
      (.withdraw (Sevm.argWord sevm 0).toNat paid.toNat)
      (some sevm.caller)
      (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      (RealizedSnapshot.ofState sevm.currentTarget trace.entry.state) := by
    rw [← hpreSnapshot]
    exact accounting
  have childPre := effect.acceptedPayoutChildPre bodyPrecondition rfl trace
  refine ⟨{
    paid := paid
    callPre := callPre
    callPost := callPost
    payout := trace
    childPre := childPre
    accounting := ?_
    postStor := hpostStor
    postBalance := hpostBalance }⟩
  · exact accounting'

/-- A positive world-state credit that leaves PRORATA storage fixed is the
frozen external-credit accounting class. -/
theorem accountingEffect_externalCredit
    {ca : Adr} {pre post : State} {amount : Nat} {actor : Option Adr}
    (hstor : post.getStor ca = pre.getStor ca)
    (hbalance : (post.bal ca).toNat = (pre.bal ca).toNat + amount)
    (hpositive : 0 < amount) :
    RealizedEffect offset.toNat (.externalCredit amount) actor
      (RealizedSnapshot.ofState ca pre) (RealizedSnapshot.ofState ca post) := by
  refine ⟨?_, ?_⟩
  · rw [RealizedSnapshot.ofState_snapshot, RealizedSnapshot.ofState_snapshot,
      hstor, hbalance]
    exact .externalCredit _ _ _ hpositive
  · show (RealizedSnapshot.ofState ca post).ledger =
      (RealizedSnapshot.ofState ca pre).ledger
    rw [RealizedSnapshot.ofState_ledger, RealizedSnapshot.ofState_ledger, hstor]

/-- A boundary preserving the target storage and balance is exactly silent in
the four-way accounting vocabulary. -/
theorem accountingEffect_silent
    {ca : Adr} {pre post : State} {actor : Option Adr}
    (hstor : post.getStor ca = pre.getStor ca)
    (hbalance : post.bal ca = pre.bal ca) :
    RealizedEffect offset.toNat .silent actor
      (RealizedSnapshot.ofState ca pre) (RealizedSnapshot.ofState ca post) := by
  refine ⟨?_, ?_⟩
  · rw [RealizedSnapshot.ofState_snapshot, RealizedSnapshot.ofState_snapshot,
      hstor, hbalance]
    exact .silent _
  · show (RealizedSnapshot.ofState ca post).ledger =
      (RealizedSnapshot.ofState ca pre).ledger
    rw [RealizedSnapshot.ofState_ledger, RealizedSnapshot.ofState_ledger, hstor]

/-- A nonpayable observation with unchanged target state is silent from its
semantic (pre-credit) entry as well. -/
theorem accountingEffect_silentBeforeCredit
    {sevm : Sevm} {pre post : Devm} {actor : Option Adr}
    (hvalue : sevm.value = 0)
    (hstor : Devm.getStor post sevm.currentTarget =
      Devm.getStor pre sevm.currentTarget)
    (hbalance : Devm.getBal post sevm.currentTarget =
      Devm.getBal pre sevm.currentTarget) :
    RealizedEffect offset.toNat .silent actor
      (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      (RealizedSnapshot.ofState sevm.currentTarget post.state) := by
  rw [show RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
      pre.state = RealizedSnapshot.ofState sevm.currentTarget pre.state
    from by
      unfold RealizedSnapshot.beforeCredit RealizedSnapshot.ofState
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
      RealizedEffect offset.toNat kind (some sevm.caller)
        (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state)
        (RealizedSnapshot.ofState sevm.currentTarget post.state) := by
  rcases entry.donatePersistentEq with ⟨hstor, hbal⟩
  let supply := supplyN (Devm.getStor pre sevm.currentTarget)
  let balance := (Devm.getBal pre sevm.currentTarget).toNat
  let amount := sevm.value.toNat
  have hpostSnapshot :
      (RealizedSnapshot.ofState sevm.currentTarget post.state).snapshot =
        ⟨supply, balance⟩ := by
    rw [RealizedSnapshot.ofState_snapshot]
    exact congrArg₂ AccountingSnapshot.mk
      (by
        change supplyN (Devm.getStor post sevm.currentTarget) = supply
        rw [congrFun hstor sevm.currentTarget])
      (by
        change (Devm.getBal post sevm.currentTarget).toNat = balance
        rw [congrFun hbal sevm.currentTarget])
  have hpostLedger :
      (RealizedSnapshot.ofState sevm.currentTarget post.state).ledger =
        (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state).ledger := by
    rw [RealizedSnapshot.ofState_ledger, RealizedSnapshot.beforeCredit_ledger]
    exact congrArg Stor.rest (congrFun hstor sevm.currentTarget)
  have hcredited : balance - amount + amount = balance :=
    Nat.sub_add_cancel invariant.value_le_balance
  by_cases hpositive : 0 < amount
  · refine ⟨.externalCredit amount, ?_, hpostLedger⟩
    rw [show (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
        pre.state).snapshot = ⟨supply, balance - amount⟩ from rfl,
      hpostSnapshot]
    simpa only [hcredited] using
      (ProrataAccountingEffect.externalCredit
        supply (balance - amount) amount hpositive)
  · have hzero : amount = 0 := Nat.eq_zero_of_not_pos hpositive
    refine ⟨.silent, ?_, hpostLedger⟩
    rw [show (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
        pre.state).snapshot = ⟨supply, balance - amount⟩ from rfl,
      hpostSnapshot, hzero]
    exact .silent _

/-- The successful shares preview is a silent accounting observation. -/
theorem BodyEntry.sharesAccountingEffect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (entry : BodyEntry fs sevm pre post convertToShares)
    (hvalue : sevm.value = 0) :
    RealizedEffect offset.toNat .silent (some sevm.caller)
      (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      (RealizedSnapshot.ofState sevm.currentTarget post.state) := by
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
    RealizedEffect offset.toNat .silent (some sevm.caller)
      (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value pre.state)
      (RealizedSnapshot.ofState sevm.currentTarget post.state) := by
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
    RealizedSnapshot → List (ProrataAccountingStep o) →
      RealizedSnapshot → Prop where
  | nil (boundary : RealizedSnapshot) :
      ProrataAccountingReplay o boundary [] boundary
  | cons {pre mid post : RealizedSnapshot} {step : ProrataAccountingStep o}
      {steps : List (ProrataAccountingStep o)}
      (pre_eq : step.pre = pre.snapshot)
      (post_eq : step.post = mid.snapshot)
      (ledger : LedgerMove step.kind step.provenance.actor
        pre.ledger mid.ledger)
      (tail : ProrataAccountingReplay o mid steps post) :
      ProrataAccountingReplay o pre (step :: steps) post

namespace ProrataAccountingReplay

/-- One realized effect is a connected singleton replay. -/
theorem singleton {o : Nat} {pre post : RealizedSnapshot}
    {kind : ProrataAccountingKind}
    (provenance : ProrataAccountingProvenance)
    (realized : RealizedEffect o kind provenance.actor pre post) :
    ProrataAccountingReplay o pre
      [{ pre := pre.snapshot, post := post.snapshot, kind, provenance,
          effect := realized.effect }] post :=
  ProrataAccountingReplay.cons rfl rfl realized.ledger
    (ProrataAccountingReplay.nil post)

/-- Concatenate two accounting replays at their shared boundary. -/
theorem append {o : Nat} {pre mid post : RealizedSnapshot}
    {left right : List (ProrataAccountingStep o)}
    (before : ProrataAccountingReplay o pre left mid)
    (after : ProrataAccountingReplay o mid right post) :
    ProrataAccountingReplay o pre (left ++ right) post := by
  induction before with
  | nil boundary =>
      simpa using after
  | cons pre_eq post_eq ledger tail ih =>
      simpa using ProrataAccountingReplay.cons pre_eq post_eq ledger (ih after)

/-- Equal realized boundaries contribute no accounting step. -/
theorem nil_of_eq {o : Nat} {pre post : RealizedSnapshot}
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
        (RealizedSnapshot.ofState ca pre) steps
        (RealizedSnapshot.ofState ca (debit.addBal target value)) := by
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
          RealizedSnapshot.ofState ca (debit.addBal ca value) =
            RealizedSnapshot.ofState ca pre := by
        unfold RealizedSnapshot.ofState
        exact congrArg₂ RealizedSnapshot.mk
          (fields.1 ca)
          (by rw [balance_eq, zero, Nat.add_zero])
      exact ⟨[], nil_of_eq snapshot_eq⟩
  · have balance_eq :
        (debit.addBal target value).bal ca = pre.bal ca :=
      of_transfer_bal_other sub caller_ne target_eq
    have snapshot_eq :
        RealizedSnapshot.ofState ca (debit.addBal target value) =
          RealizedSnapshot.ofState ca pre := by
      unfold RealizedSnapshot.ofState
      exact congrArg₂ RealizedSnapshot.mk
        (fields.1 ca)
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
        (RealizedSnapshot.ofState ca pre) steps
        (RealizedSnapshot.ofState ca (pre.addBal target value)) := by
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
          RealizedSnapshot.ofState ca (pre.addBal ca value) =
            RealizedSnapshot.ofState ca pre := by
        unfold RealizedSnapshot.ofState
        exact congrArg₂ RealizedSnapshot.mk
          storage_eq
          (by rw [balance_eq, zero, Nat.add_zero])
      exact ⟨[], nil_of_eq snapshot_eq⟩
  · have balance_eq : (pre.addBal target value).bal ca = pre.bal ca := by
      show ((pre.setBal target (pre.bal target + value)).get ca).bal = _
      rw [State.setBal_get_ne target_eq]
      rfl
    have snapshot_eq :
        RealizedSnapshot.ofState ca (pre.addBal target value) =
          RealizedSnapshot.ofState ca pre := by
      unfold RealizedSnapshot.ofState
      exact congrArg₂ RealizedSnapshot.mk
        storage_eq
        (congrArg B256.toNat balance_eq)
    exact ⟨[], nil_of_eq snapshot_eq⟩

/-- Any projected transition that fixes PRORATA storage and cannot lower its
balance is either one positive external credit or no accounting step at all.
This endpoint lemma lets foreign opcode proofs expose only their two relevant
facts instead of duplicating the four-way classifier. -/
theorem of_storage_eq_balance_mono
    {ca : Adr} {pre post : State}
    (provenance : ProrataAccountingProvenance)
    (storage_eq : post.getStor ca = pre.getStor ca)
    (balance_mono : (pre.bal ca).toNat ≤ (post.bal ca).toNat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca pre) steps
        (RealizedSnapshot.ofState ca post) := by
  let amount := (post.bal ca).toNat - (pre.bal ca).toNat
  have balance_eq :
      (post.bal ca).toNat = (pre.bal ca).toNat + amount := by
    dsimp only [amount]
    omega
  by_cases positive : 0 < amount
  · exact ⟨_, singleton provenance
      (accountingEffect_externalCredit storage_eq balance_eq positive)⟩
  · have zero : amount = 0 := Nat.eq_zero_of_not_pos positive
    have snapshot_eq :
        RealizedSnapshot.ofState ca post =
          RealizedSnapshot.ofState ca pre := by
      unfold RealizedSnapshot.ofState
      exact congrArg₂ RealizedSnapshot.mk
        storage_eq
        (by rw [balance_eq, zero, Nat.add_zero])
    exact ⟨[], nil_of_eq snapshot_eq⟩

/-- Every replay yields the frozen connected-path carrier used by the exact
dust theorem; no boundary connectivity is reconstructed axiomatically. -/
theorem exists_path {o : Nat} {pre post : RealizedSnapshot}
    {steps : List (ProrataAccountingStep o)}
    (replay : ProrataAccountingReplay o pre steps post) :
    ∃ path : ProrataAccountingPath o,
      path.steps = steps ∧ path.first = pre.snapshot ∧
        path.last = post.snapshot := by
  induction replay with
  | nil boundary =>
      exact ⟨ProrataAccountingPath.nil o boundary.snapshot, rfl, rfl, rfl⟩
  | @cons pre mid post step steps pre_eq post_eq _ tail ih =>
      rcases ih with ⟨path, hsteps, hfirst, hlast⟩
      have connect : step.post = path.first := post_eq.trans hfirst.symm
      refine ⟨ProrataAccountingPath.cons step path connect, ?_, ?_, ?_⟩
      · rw [ProrataAccountingPath.cons]
        simp only
        rw [hsteps]
      · exact pre_eq
      · simpa using hlast

end ProrataAccountingReplay

/-- Prefixing the recursively replayed callback with its realized withdrawal
step yields the complete accounting replay of the enclosing PRORATA frame. -/
theorem RealizedWithdrawal.accountingReplay
    {sevm : Sevm} {pre post : Devm}
    (withdrawal : RealizedWithdrawal sevm pre post)
    (provenance : ProrataAccountingProvenance)
    (actor : provenance.actor = some sevm.caller)
    (childReplay : ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState sevm.currentTarget
          withdrawal.payout.entry.state)
        steps
        (RealizedSnapshot.ofState sevm.currentTarget
          withdrawal.payout.child.state)) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state)
        steps (RealizedSnapshot.ofState sevm.currentTarget post.state) := by
  rcases childReplay with ⟨steps, replay⟩
  have combined :=
    (ProrataAccountingReplay.singleton provenance
      (withdrawal.accounting.of_actor_eq actor)).append replay
  rw [withdrawal.postSnapshot]
  exact ⟨_, combined⟩

/-- Every successful nonrecursive instruction in a foreign frame realizes
exactly the projected PRORATA accounting change: either a positive external
credit or no accounting step. -/
theorem Ninst.foreignNoneAccountingReplay
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    (provenance : ProrataAccountingProvenance) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca pre.state) steps
        (RealizedSnapshot.ofState ca post.state) := by
  exact ProrataAccountingReplay.of_storage_eq_balance_mono provenance
    (_root_.Blanc.Ninst.foreignNone_getStor_eq run target_ne)
    (_root_.Blanc.Ninst.targetBalanceMono_of_none run target_ne sum_nof)

/-- Every successful terminal instruction in a foreign frame realizes exactly
one projected PRORATA external credit or no accounting step. -/
theorem Linst.foreignAccountingReplay
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.Run sevm pre l (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    (provenance : ProrataAccountingProvenance) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca pre.state) steps
        (RealizedSnapshot.ofState ca post.state) := by
  exact ProrataAccountingReplay.of_storage_eq_balance_mono provenance
    (congrFun (_root_.Blanc.Linst.getStor_eq run) ca)
    (_root_.Blanc.Linst.targetBalanceMono_of_foreign
      run target_ne sum_nof)

/-- Every successful deployed route except withdrawal is already a complete
singleton accounting replay.  The withdrawal arm is retained for the
settlement-aware child recursion that follows. -/
theorem ProrataMainRoute.accountingReplay_or_withdraw
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (route : ProrataMainRoute fs sevm pre post)
    (invariant : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget))
    (provenance : ProrataAccountingProvenance)
    (actor : provenance.actor = some sevm.caller) :
    (∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.beforeCredit sevm.currentTarget sevm.value
          pre.state)
        steps (RealizedSnapshot.ofState sevm.currentTarget post.state)) ∨
      Nonempty (BodyEntry fs sevm pre post Prorata.withdraw) ∧
        sevm.value = 0 := by
  cases route with
  | deposit entry =>
      rcases entry.depositAccountingEffect invariant with ⟨minted, effect⟩
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance
          (effect.of_actor_eq actor)⟩
  | withdraw hvalue entry =>
      exact Or.inr ⟨⟨entry⟩, hvalue⟩
  | convertToShares hvalue entry =>
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance
          ((entry.sharesAccountingEffect hvalue).of_actor_eq actor)⟩
  | convertToAssets hvalue entry =>
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance
          ((entry.assetsAccountingEffect hvalue).of_actor_eq actor)⟩
  | donate entry =>
      rcases entry.donateAccountingEffect invariant with ⟨kind, effect⟩
      exact Or.inl ⟨_,
        ProrataAccountingReplay.singleton provenance
          (effect.of_actor_eq actor)⟩

/-- An exact retained PRORATA frame is either already a complete replay or is
the unique withdrawal shape whose paid child trace must be replayed next. -/
theorem Exec.Frame.accountingReplay_or_realizedWithdrawal
    {ca : Adr} {frame : Exec.Frame}
    (invocation : frame.exactInvocation prorata ca ca)
    (precondition : prorataSpec.Pre ca frame.sevm frame.pre)
    (provenance : ProrataAccountingProvenance)
    (actor : provenance.actor = some frame.sevm.caller)
    (recipient_ne : frame.sevm.caller.toB256.toAdr ≠ ca) :
    (∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.beforeCredit ca frame.sevm.value frame.pre.state)
        steps (RealizedSnapshot.ofState ca frame.post.state)) ∨
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
  rcases route.accountingReplay_or_withdraw invariant provenance actor with
      replay | ⟨⟨entry⟩, hvalue⟩
  · left
    simpa only [target_eq] using replay
  · right
    have precondition' :
        prorataSpec.Pre frame.sevm.currentTarget frame.sevm frame.pre := by
      simpa only [target_eq] using precondition
    have recipient_ne' :
        frame.sevm.caller.toB256.toAdr ≠ frame.sevm.currentTarget := by
      simpa only [target_eq] using recipient_ne
    exact entry.realizedWithdrawal hvalue invariant precondition' recipient_ne'

end Prorata

end Blanc
