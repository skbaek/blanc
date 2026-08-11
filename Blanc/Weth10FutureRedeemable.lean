import Blanc.Weth10Hardened
import Blanc.Weth10Redeemable
import Blanc.Weth10DeploymentRoot

/-!
Deployment-rooted future redemption for the exact Blanc WETH10 runtime.

This module assembles the flagship guarantee: from a deployment root and any
two configured Prague-only legs — one to a checkpoint, one onward to an
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
    {chainId : UInt64} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory chainId dp ca checkpoint future} {msg : Msg}
    (hroot : Weth10.DeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hq : q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleRedemptionMessage
      dp ca u recipient q future.state msg) :
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
    {chainId : UInt64} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory chainId dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hq : q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleRedemptionTx
      dp ca u recipient q benv bout tx index) :
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
    (chainId : UInt64) (dp : DeployParams) (ca u : Adr)
    (checkpoint future : BlockChain)
    (history : AccountedHistory chainId dp ca checkpoint future) : Prop where
  futureStable : Weth10.Stable dp ca future.state
  reachable : BlockChain.ReachUsing
    (ChainConfig.pragueOnly chainId) checkpoint future
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
  messageEnabled : ∀ (q : Nat) (recipient : Adr) (msg : Msg),
    q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut) ->
    AdmissibleRedemptionMessage dp ca u recipient q future.state msg ->
    MessageRedemptionEnabled dp ca u recipient q future.state msg
  transactionEnabled : ∀ (q : Nat) (recipient : Adr)
      (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat),
    benv.state = future.state ->
    q <= bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut) ->
    AdmissibleRedemptionTx dp ca u recipient q benv bout tx index ->
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index

/-- The flagship: a deployment root, a leg to a checkpoint and a further leg
to an arbitrary future snapshot yield an accounted history of the second leg
carrying the whole guarantee.

The history is existential because it is recovered from the reachability
derivation rather than reconstructed from the endpoints; that is what makes
this a logical guarantee about the window and not a trace extractor. -/
theorem deployment_reachable_future_redeemable
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : Weth10.DeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) checkpoint future) :
    ∃ history, FutureRedemptionGuarantee
      chainId dp ca u checkpoint future history := by
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
  · exact fun _ _ _ hq henv =>
      deployment_reachable_residual_messageRedemption_enabled
        hroot hcheckpoint hq henv
  · exact fun _ _ _ _ _ _ hentry hq henv =>
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
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed : BlockChain}
    (hroot : Weth10.DeploymentRoot chainId base deployed dp ca) :
    AllowanceQuiescent ca u deployed.state := by
  intro owner spender _
  rw [hroot.emptyStorage]
  rfl

/-- The full-window corollary: with the deployment itself as the checkpoint,
the guarantee holds over the contract's whole life and its window starts
allowance-quiescent. -/
theorem deployment_fullWindow_future_redeemable
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future) :
    AllowanceQuiescent ca u deployed.state ∧
      ∃ history, FutureRedemptionGuarantee
        chainId dp ca u deployed future history :=
  ⟨deploymentRoot_allowanceQuiescent hroot,
    deployment_reachable_future_redeemable hroot hroot.reflReach hfuture⟩

end Weth10

end Blanc
