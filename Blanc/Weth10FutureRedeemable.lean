import Blanc.Weth10Dormant
import Blanc.Weth10Redeemable
import Blanc.Weth10DeploymentRoot

/-!
Deployment-rooted future redemption for the exact Blanc WETH10 runtime.

This module assembles the flagship guarantee: from a deployment root and any
two configured-schedule legs — one to a checkpoint, one onward to an
arbitrary future snapshot — a holder's booked balance at the checkpoint is
still covered at the future snapshot, up to the outflow that the runtime
itself authorized, and every residual unit remains redeemable there.

Three things about the shape of the guarantee are deliberate.

The history is *obtained*, not computed.  `AccountedHistory` is produced by
recursion over the reachability derivation, so the guarantee is a logical
statement about the window rather than an extractor that reconstructs a trace
from the endpoints.  Nothing downstream may read the history's internals.

Collision-freedom is confined to one field.  `hardenedDescription` takes
`NoAllowanceKeyCollision` as its own hypothesis; the guarantee does not.  In
particular neither enabledness field depends on it: a holder's ability to
redeem the residual never rests on an assumption about hash keys.  Only the
*attribution* of the outflow to identified authorizing acts does.

The balance surface is `bookedBalanceNat` throughout.  The conservation
development ships no separate `holderBookedNat`, so no bridge lemma stands
between the conservation results and the redemption results.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Composing configured reachability

`BlockChain.ReachUsing`'s `refl` constructor carries the schedule validity,
context validity and chain-identity evidence of its own snapshot, so composing
two legs needs nothing beyond replaying the second leg's steps on top of the
first. -/

private theorem reachUsing_trans {cfg : ChainConfig} {a b c : BlockChain}
    (hab : BlockChain.ReachUsing cfg a b)
    (hbc : BlockChain.ReachUsing cfg b c) :
    BlockChain.ReachUsing cfg a c := by
  induction hbc with
  | refl _ _ _ => exact hab
  | step _ hbound htransition ih => exact .step ih hbound htransition

/-! ## The low-level enabledness capstones

Both take the residual bound at the *checkpoint* and discharge redemption at
the *future* snapshot.  The bridge is the truncated floor: whatever the window
did, the checkpoint balance minus the window's permanent outflow is still
present at the end. -/

/-- A deployment-rooted holder can spend its checkpoint residual through a
fresh admissible redemption message at any later snapshot the accounted
history reaches.  The residual bound is stated at the checkpoint; the
enabledness conclusion is at the future snapshot. -/
theorem deployment_reachable_residual_messageRedemption_enabled
    {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future} {msg : Msg}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg := by
  have hcheckpointStable : Stable dp ca checkpoint.state :=
    hroot.reachable_stable hcheckpoint
  have hfutureStable : Stable dp ca future.state :=
    hroot.reachable_stable (reachUsing_trans hcheckpoint history.toReachUsing)
  have hfloor := holderFlow_truncated_floor hcheckpointStable history (u := u)
  exact hfutureStable.messageRedemption_enabled_of_le
    (Nat.le_trans hq hfloor) henv

/-- The transaction-level counterpart: the same checkpoint residual bound
enables a whole admissible redemption transaction whose entry state is the
future snapshot. -/
theorem deployment_reachable_residual_transactionRedemption_enabled
    {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index := by
  have hcheckpointStable : Stable dp ca checkpoint.state :=
    hroot.reachable_stable hcheckpoint
  have hentryStable : Stable dp ca benv.state := by
    rw [hentry]
    exact hroot.reachable_stable
      (reachUsing_trans hcheckpoint history.toReachUsing)
  have hfloor := holderFlow_truncated_floor hcheckpointStable history (u := u)
  refine hentryStable.transactionRedemption_enabled_of_le ?_ henv
  rw [hentry]
  exact Nat.le_trans hq hfloor

/-- The checkpoint residual is also enabled through the direct-holder
`withdraw(q)` message selector. -/
theorem deployment_reachable_residual_selfMessageRedemption_enabled
    {cfg : ChainConfig} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future} {msg : Msg}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleSelfRedemptionMessage rules dp ca u q future.state msg) :
    MessageRedemptionEnabled dp ca u u q future.state msg := by
  have hcheckpointStable : Stable dp ca checkpoint.state :=
    hroot.reachable_stable hcheckpoint
  have hfutureStable : Stable dp ca future.state :=
    hroot.reachable_stable (reachUsing_trans hcheckpoint history.toReachUsing)
  have hfloor := holderFlow_truncated_floor hcheckpointStable history (u := u)
  exact hfutureStable.selfRedemption_enabled_of_le
    (Nat.le_trans hq hfloor) henv

/-- The transaction-altitude counterpart for the direct-holder
`withdraw(q)` selector. -/
theorem deployment_reachable_residual_selfTransactionRedemption_enabled
    {cfg : ChainConfig} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index := by
  have hcheckpointStable : Stable dp ca checkpoint.state :=
    hroot.reachable_stable hcheckpoint
  have hentryStable : Stable dp ca benv.state := by
    rw [hentry]
    exact hroot.reachable_stable
      (reachUsing_trans hcheckpoint history.toReachUsing)
  have hfloor := holderFlow_truncated_floor hcheckpointStable history (u := u)
  refine hentryStable.selfTransactionRedemption_enabled_of_le ?_ henv
  rw [hentry]
  exact Nat.le_trans hq hfloor

/-- Rebasing the window at the future itself collapses the outflow terms, so
the *entire booked balance* at any reachable snapshot — not merely a
checkpoint residual — is message-redemption enabled there. -/
theorem deployment_reachable_booked_messageRedemption_enabled
    {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain} {msg : Msg}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hq : q <= bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionMessage rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  (hroot.reachable_stable hfuture).messageRedemption_enabled_of_le hq henv

/-- The transaction-level counterpart of the rebased bound: the full booked
balance at any reachable snapshot is transaction-redemption enabled from that
snapshot as the entry state. -/
theorem deployment_reachable_booked_transactionRedemption_enabled
    {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hentry : benv.state = future.state)
    (hq : q <= bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionTx rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index := by
  have hstable : Stable dp ca benv.state := by
    rw [hentry]
    exact hroot.reachable_stable hfuture
  refine hstable.transactionRedemption_enabled_of_le ?_ henv
  rw [hentry]
  exact hq

/-- In a rebased future window, the holder's full booked balance is enabled
through `withdraw(q)` at transaction altitude. -/
theorem deployment_reachable_booked_selfTransactionRedemption_enabled
    {cfg : ChainConfig} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hentry : benv.state = future.state)
    (hq : q <= bookedBalanceNat future.state ca u)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index := by
  have hstable : Stable dp ca benv.state := by
    rw [hentry]
    exact hroot.reachable_stable hfuture
  refine hstable.selfTransactionRedemption_enabled_of_le ?_ henv
  rw [hentry]
  exact hq

/-- For a funded holder admitted by Jaune's exact sender boundary, with the
canonical payload, nonce, fees and gas envelope, sender recovery is the only
missing input between the holder and transaction-altitude redemption. -/
theorem deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender
    {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {maxPriorityFee maxFee : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hentry : benv.state = future.state)
    (hq : q <= bookedBalanceNat future.state ca u)
    (henv : NonSignatureRedemptionTxEnvelope
      rules dp ca u recipient q benv bout tx index maxPriorityFee maxFee)
    (hrecovered : recoverSender benv.stat.chainId tx = .ok u) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_booked_transactionRedemption_enabled
    hroot hfuture hentry hq (henv.admissible_of_recoveredSender hrecovered)

/-! ## The flagship guarantee -/

/-- Everything a checkpoint holder is promised about an arbitrary reachable
future, packaged over the accounted history of the window.

`conserved` and `residualFloor` are the conservation surface; `messageEnabled`
and `transactionEnabled` are the redemption surface, and neither takes a
collision hypothesis.  `hardenedDescription` is the only field that mentions
`NoAllowanceKeyCollision`, and it takes it as its own hypothesis, so a caller
that cannot discharge collision-freedom still gets the floor and the
redeemability. -/
structure FutureRedemptionGuarantee
    (cfg : ChainConfig) (dp : DeployParams) (ca u : Adr)
    (checkpoint future : BlockChain)
    (history : AccountedHistory cfg dp ca checkpoint future) : Prop where
  futureStable : Weth10.Stable dp ca future.state
  reachable : BlockChain.ReachUsing cfg checkpoint future
  conserved :
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut
  residualFloor :
    bookedBalanceNat checkpoint.state ca u <=
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut
  hardenedDescription :
    NoAllowanceKeyCollision history ->
      (history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut =
        hardenedOutflow history u
  messageEnabled : ∀ (rules : ForkRules) (q : Nat) (recipient : Adr) (msg : Msg),
    q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut) ->
    AdmissibleRedemptionMessage rules dp ca u recipient q future.state msg ->
    MessageRedemptionEnabled dp ca u recipient q future.state msg
  transactionEnabled : ∀ (rules : ForkRules) (q : Nat) (recipient : Adr)
      (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat),
    benv.state = future.state ->
    q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut) ->
    AdmissibleRedemptionTx rules dp ca u recipient q benv bout tx index ->
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index

/-- The flagship redemption package with both public selectors present at
message and transaction altitude.  The inherited guarantee carries
`withdrawTo`; these two fields add direct-holder `withdraw`. -/
structure FutureDualSelectorRedemptionGuarantee
    (cfg : ChainConfig) (dp : DeployParams) (ca u : Adr)
    (checkpoint future : BlockChain)
    (history : AccountedHistory cfg dp ca checkpoint future) : Prop where
  toFutureRedemptionGuarantee :
    FutureRedemptionGuarantee cfg dp ca u checkpoint future history
  selfMessageEnabled : ∀ (rules : ForkRules) (q : Nat) (msg : Msg),
    q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut) ->
    AdmissibleSelfRedemptionMessage rules dp ca u q future.state msg ->
    MessageRedemptionEnabled dp ca u u q future.state msg
  selfTransactionEnabled : ∀ (rules : ForkRules) (q : Nat) (benv : Benv)
      (bout : BlockOutput) (tx : Tx) (index : Nat),
    benv.state = future.state ->
    q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut) ->
    AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index ->
    TransactionRedemptionEnabled dp ca u u q benv bout tx index

/-- The flagship: a deployment root, a leg to a checkpoint and a further leg
to an arbitrary future snapshot yield an accounted history of the second leg
carrying the whole guarantee.

The history is existential because it is recovered from the reachability
derivation rather than reconstructed from the endpoints; that is what makes
this a logical guarantee about the window and not a trace extractor. -/
theorem deployment_reachable_future_redeemable
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hfuture : BlockChain.ReachUsing cfg checkpoint future) :
    ∃ history, FutureRedemptionGuarantee
      cfg dp ca u checkpoint future history := by
  have hcheckpointStable : Stable dp ca checkpoint.state :=
    hroot.reachable_stable hcheckpoint
  have hfutureStable : Stable dp ca future.state :=
    hroot.reachable_stable (reachUsing_trans hcheckpoint hfuture)
  obtain ⟨history⟩ :=
    exists_accountedHistory_of_reachUsing (dp := dp) (ca := ca)
      hcheckpointStable hfuture
  refine ⟨history, hfutureStable, hfuture, ?_, ?_, ?_, ?_, ?_⟩
  · exact (holderFlow_flash_cancelled hcheckpointStable history).2
  · have hfloor := holderFlow_residual_floor hcheckpointStable history (u := u)
    omega
  · exact fun hnc =>
      permanentOutflow_eq_hardenedOutflow_of_noCollision
        hcheckpointStable history hnc
  · exact fun _ _ _ _ hq henv =>
      deployment_reachable_residual_messageRedemption_enabled
        hroot hcheckpoint hq henv
  · exact fun _ _ _ _ _ _ _ hentry hq henv =>
      deployment_reachable_residual_transactionRedemption_enabled
        hroot hcheckpoint hq hentry henv

/-- The dual-selector flagship: the same accounted history packages
`withdrawTo` and direct-holder `withdraw` at both altitudes. -/
theorem deployment_reachable_future_dualSelector_redeemable
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hfuture : BlockChain.ReachUsing cfg checkpoint future) :
    ∃ history, FutureDualSelectorRedemptionGuarantee
      cfg dp ca u checkpoint future history := by
  rcases deployment_reachable_future_redeemable
      hroot hcheckpoint hfuture with ⟨history, hguarantee⟩
  refine ⟨history, hguarantee, ?_, ?_⟩
  · exact fun _ _ _ hq henv =>
      deployment_reachable_residual_selfMessageRedemption_enabled
        hroot hcheckpoint hq henv
  · exact fun _ _ _ _ _ _ hentry hq henv =>
      deployment_reachable_residual_selfTransactionRedemption_enabled
        hroot hcheckpoint hq hentry henv

/-- The simultaneous form of the flagship: because the accounted history is
recovered from the reachability derivation alone, one history carries the
whole guarantee for *every* holder at once — `∃ history, ∀ u`, not merely
`∀ u, ∃ history`. -/
theorem deployment_reachable_future_redeemable_allHolders
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hfuture : BlockChain.ReachUsing cfg checkpoint future) :
    ∃ history, ∀ u : Adr, FutureRedemptionGuarantee
      cfg dp ca u checkpoint future history := by
  have hcheckpointStable : Stable dp ca checkpoint.state :=
    hroot.reachable_stable hcheckpoint
  have hfutureStable : Stable dp ca future.state :=
    hroot.reachable_stable (reachUsing_trans hcheckpoint hfuture)
  obtain ⟨history⟩ :=
    exists_accountedHistory_of_reachUsing (dp := dp) (ca := ca)
      hcheckpointStable hfuture
  refine ⟨history, ?_⟩
  intro u
  refine ⟨hfutureStable, hfuture, ?_, ?_, ?_, ?_, ?_⟩
  · exact (holderFlow_flash_cancelled hcheckpointStable history).2
  · have hfloor := holderFlow_residual_floor hcheckpointStable history (u := u)
    omega
  · exact fun hnc =>
      permanentOutflow_eq_hardenedOutflow_of_noCollision
        hcheckpointStable history hnc
  · exact fun _ _ _ _ hq henv =>
      deployment_reachable_residual_messageRedemption_enabled
        hroot hcheckpoint hq henv
  · exact fun _ _ _ _ _ _ _ hentry hq henv =>
      deployment_reachable_residual_transactionRedemption_enabled
        hroot hcheckpoint hq hentry henv

/-! ## The deployment-rooted full window

Taking the deployment itself as the checkpoint makes the guarantee's window
the contract's whole life.  In that case the checkpoint carries no allowance
state at all, so the attribution taxonomy has nothing to inherit: every
authorizing act inside the window is an act *of* the window. -/

/-- A deployment root's storage at the contract is empty, so every allowance
slot — over every raw owner word normalizing to the holder and every spender
word — is zero.  This is what makes the deployment-rooted window a full-window
attribution: no allowance predates it. -/
theorem deploymentRoot_allowanceQuiescent
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca) :
    AllowanceQuiescent ca u deployed.state := by
  intro owner spender _
  rw [hroot.emptyStorage]
  rfl

/-- The full-window corollary: with the deployment itself as the checkpoint,
the guarantee holds over the contract's whole life and its window starts
allowance-quiescent. -/
theorem deployment_fullWindow_future_redeemable
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future) :
    AllowanceQuiescent ca u deployed.state ∧
      ∃ history, FutureRedemptionGuarantee
        cfg dp ca u deployed future history :=
  ⟨deploymentRoot_allowanceQuiescent hroot,
    deployment_reachable_future_redeemable hroot hroot.reflReach hfuture⟩

/-- In a deployment-rooted history, no nonzero delegated permanent outflow
can retain the empty deployment checkpoint as its governing allowance root. -/
theorem deployment_fullWindow_attributionRootAt_ne_checkpoint
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    {earlier later : List CountedFrame} {record : CountedFrame}
    {action : FlowAction} {debit : DebitProvenance}
    {event : AllowanceEvent}
    (hsplit : history.attributionLedger = earlier ++ record :: later)
    (hout : record.permanentOutflow u ≠ 0)
    (haction : record.action = some action)
    (hdebit : action.debit = some debit)
    (hevent : record.allowance = some event)
    (hkey : delegatedKey? debit.branch = some event.key) :
    attributionRootAt earlier.reverse event.key ≠ .checkpoint :=
  history.attributionRootAt_ne_checkpoint_of_emptyStorage
    hroot.stable hroot.emptyStorage hsplit hout haction hdebit hevent hkey

/-- Whole-life collision freedom leaves exactly three authorization classes
for every nonzero permanent-outflow record: the holder's own call, an
in-window `approve`, or an in-window `permit` signature. -/
theorem deployment_fullWindow_permanentOutflowAuthorization
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    {earlier later : List CountedFrame} {record : CountedFrame}
    (hsplit : history.attributionLedger = earlier ++ record :: later)
    (hout : record.permanentOutflow u ≠ 0) :
    PermanentOutflowAuthorization record earlier.reverse u :=
  history.permanentOutflowAuthorization_of_emptyStorage
    hroot.stable hroot.emptyStorage hnc hsplit hout

/-- The complete full-window hardened description: its numeric sub-sum is the
whole permanent outflow, and every nonzero contributing record has only a
direct, `approve`, or `permit` authorization root. -/
theorem deployment_fullWindow_hardenedOutflow_only_authorizingRoots
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history) :
    ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut =
      hardenedOutflow history u) ∧
      ∀ earlier record later,
        history.attributionLedger = earlier ++ record :: later →
        record.permanentOutflow u ≠ 0 →
        PermanentOutflowAuthorization record earlier.reverse u := by
  constructor
  · exact permanentOutflow_eq_hardenedOutflow_of_noCollision
      hroot.stable history hnc
  · intro earlier record later hsplit hout
    exact deployment_fullWindow_permanentOutflowAuthorization
      hroot history hnc hsplit hout

/-- In a deployment-rooted full window, collision freedom and the absence of
effectful authorization by `u` suffice for booked-balance monotonicity; the
deployment root discharges allowance quiescence. -/
theorem deployment_fullWindow_dormant_holder_balance_monotone
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    (hdormant : NoAuthorizingActBy u history) :
    bookedBalanceNat deployed.state ca u ≤
      bookedBalanceNat future.state ca u :=
  dormant_holder_balance_monotone hroot.stable history hnc
    (deploymentRoot_allowanceQuiescent hroot) hdormant

/-- Reachability constructs the authentic full-window history; only its
trace-local collision property and the holder's effective dormancy remain as
conditional premises. -/
theorem deployment_reachable_dormant_holder_balance_monotone
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future) :
    ∃ history : AccountedHistory cfg dp ca deployed future,
      NoAllowanceKeyCollision history →
      NoAuthorizingActBy u history →
      bookedBalanceNat deployed.state ca u ≤
        bookedBalanceNat future.state ca u := by
  obtain ⟨history⟩ :=
    exists_accountedHistory_of_reachUsing (dp := dp) (ca := ca)
      hroot.stable hfuture
  exact ⟨history, fun hnc hdormant =>
    deployment_fullWindow_dormant_holder_balance_monotone
      hroot history hnc hdormant⟩

end Weth10

end Blanc
