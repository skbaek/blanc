import Blanc.Weth10AllowanceArmsViews
import Blanc.Weth10AllowanceArmsSpendRedeem
import Blanc.Weth10AllowanceArmsCallback
import Blanc.Weth10AllowanceArmsPermit
import Blanc.Weth10AllowanceArmsFlash
import Blanc.Weth10AllowanceRecursion
import Blanc.Weth10AllowanceHistory

/-!
Selector dispatch for the allowance-region carrier.

The per-selector arms each transport the tagged allowance region across one
dispatched WETH10 selector.  This module consumes the balance development's
already-proved exhaustive partition
`Exec.Frame.callFreeStorageBranch_or_remaining` and routes each of its leaves
to the matching allowance arm, producing the contract-specific
`CompiledFrameAllowanceHandler`, then feeds that through the landed generic
chain to the history level.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Residual arm

The balance partition classifies `transfer` by its recipient argument
(`CallFreeStorageBranch.transferNonzero` versus
`RemainingStorageBranch.transferZero`) but classifies `transferAndCall` by
selector alone: its `RemainingStorageBranch.transferAndCall` leaf carries no
recipient datum.  The balance arm needs none, because
`hasProofIndexedStorageAccounting_of_transferAndCall` covers both recipients.
The allowance arm `Exec.Frame.allowanceRegionEffect_of_transferAndCall` is
stated only for a nonzero recipient, so the zero-recipient invocation —
`transferThen`'s redeem branch followed by the ERC-677 callback — is the one
leaf of the thirty with no arm.  It is quantified here rather than assumed
inside any statement below, so that discharging it in the arm modules turns
every export in this file premise-free by deleting one argument. -/

/-- The one per-selector allowance arm still missing: `transferAndCall`
invoked with a zero recipient, which runs `transferZeroThen`'s redemption
prefix and then the ERC-677 token callback. -/
def ZeroRecipientTransferAndCallAllowanceArm
    (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ frame : Exec.Frame,
    frame.AuthenticContext dp ca →
    Sevm.selector frame.sevm = transferAndCallSelector →
    frame.sevm.data.length.toB256 ≠ 0 →
    Sevm.argWord frame.sevm 0 = 0 →
    ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out) →
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run)

/-! ## Thirty-way selector dispatch -/

/-- Exact allowance-region handler for every authentic compiled WETH10 frame.
Every selector arm is discharged by its concrete chronology; the selector case
split is the balance development's already-proved partition. -/
theorem compiledFrameAllowanceHandler
    (dp : DeployParams) (ca : Adr)
    (zeroArm : ZeroRecipientTransferAndCallAllowanceArm dp ca) :
    CompiledFrameAllowanceHandler dp ca := by
  intro frame context hdeeper
  rcases frame.callFreeStorageBranch_or_remaining context with
      closed | openCase
  · cases closed with
    | receive empty =>
        exact frame.allowanceRegionEffect_of_receive context empty
    | deposit nonempty selected =>
        exact frame.allowanceRegionEffect_of_deposit context selected nonempty
    | depositTo nonempty selected =>
        exact frame.allowanceRegionEffect_of_depositTo context selected nonempty
    | transferNonzero nonempty selected recipient =>
        exact frame.allowanceRegionEffect_of_transferNonzero
          context selected nonempty recipient
    | transferFromNonzero nonempty selected recipient =>
        exact frame.allowanceRegionEffect_of_transferFromNonzero
          context selected nonempty recipient
    | noFlow branch =>
        cases branch with
        | name nonempty selected =>
            exact frame.allowanceRegionEffect_of_name
              context selected nonempty
        | approve nonempty selected =>
            exact frame.allowanceRegionEffect_of_approve
              context selected nonempty
        | totalSupply nonempty selected =>
            exact frame.allowanceRegionEffect_of_totalSupply
              context selected nonempty
        | permitTypehash nonempty selected =>
            exact frame.allowanceRegionEffect_of_permitTypehash
              context selected nonempty
        | decimals nonempty selected =>
            exact frame.allowanceRegionEffect_of_decimals
              context selected nonempty
        | domainSeparator nonempty selected =>
            exact frame.allowanceRegionEffect_of_domainSeparator
              context selected nonempty
        | maxFlashLoan nonempty selected =>
            exact frame.allowanceRegionEffect_of_maxFlashLoan
              context selected nonempty
        | balanceOf nonempty selected =>
            exact frame.allowanceRegionEffect_of_balanceOf
              context selected nonempty
        | nonces nonempty selected =>
            exact frame.allowanceRegionEffect_of_nonces
              context selected nonempty
        | callbackSuccess nonempty selected =>
            exact frame.allowanceRegionEffect_of_callbackSuccess
              context selected nonempty
        | flashMinted nonempty selected =>
            exact frame.allowanceRegionEffect_of_flashMinted
              context selected nonempty
        | symbol nonempty selected =>
            exact frame.allowanceRegionEffect_of_symbol
              context selected nonempty
        | deploymentChainId nonempty selected =>
            exact frame.allowanceRegionEffect_of_deploymentChainId
              context selected nonempty
        | flashFee nonempty selected =>
            exact frame.allowanceRegionEffect_of_flashFee
              context selected nonempty
        | allowance nonempty selected =>
            exact frame.allowanceRegionEffect_of_allowance
              context selected nonempty
  · cases openCase with
    | depositToAndCall nonempty selected =>
        exact frame.allowanceRegionEffect_of_depositToAndCall
          context selected nonempty hdeeper
    | transferZero nonempty selected recipient =>
        exact frame.allowanceRegionEffect_of_transferZero
          context selected nonempty recipient hdeeper
    | transferAndCall nonempty selected =>
        by_cases hzero : Sevm.argWord frame.sevm 0 = 0
        · exact zeroArm frame context selected nonempty hzero hdeeper
        · exact frame.allowanceRegionEffect_of_transferAndCall
            context selected nonempty hzero hdeeper
    | transferFromZero nonempty selected recipient =>
        exact frame.allowanceRegionEffect_of_transferFromZero
          context selected nonempty recipient hdeeper
    | withdraw nonempty selected =>
        exact frame.allowanceRegionEffect_of_withdraw
          context selected nonempty hdeeper
    | withdrawTo nonempty selected =>
        exact frame.allowanceRegionEffect_of_withdrawTo
          context selected nonempty hdeeper
    | withdrawFrom nonempty selected =>
        exact frame.allowanceRegionEffect_of_withdrawFrom
          context selected nonempty hdeeper
    | flashLoan nonempty selected =>
        exact frame.allowanceRegionEffect_of_flashLoan
          context selected nonempty hdeeper
    | approveAndCall nonempty selected =>
        exact frame.allowanceRegionEffect_of_approveAndCall
          context selected nonempty hdeeper
    | permit nonempty selected =>
        exact frame.allowanceRegionEffect_of_permit
          context selected nonempty hdeeper

/-! ## Lift to the history level -/

/-- Compiled-program allowance handler consumed by the generic recursion. -/
theorem compiledBodyAllowanceHandler
    (dp : DeployParams) (ca : Adr)
    (zeroArm : ZeroRecipientTransferAndCallAllowanceArm dp ca) :
    CompiledBodyAllowanceHandler dp ca :=
  (compiledFrameAllowanceHandler dp ca zeroArm).compiledBodyAllowanceHandler

/-- Complete committed allowance accounting for the installed WETH10
program. -/
theorem committedExecAllowanceSound
    (dp : DeployParams) (ca : Adr)
    (zeroArm : ZeroRecipientTransferAndCallAllowanceArm dp ca) :
    CommittedExecAllowanceSound dp ca :=
  CompiledBodyAllowanceHandler.committedExecAllowanceSound
    (compiledBodyAllowanceHandler dp ca zeroArm)

/-- Every tagged allowance key of an authentic stable-root history holds
exactly the last committed write recorded by the history's chronological
attribution ledger, or its checkpoint value when no counted write touches it.
Downstream consumers supply only the history and its stable checkpoint. -/
theorem AccountedHistory.allowanceTransported_of_compiled
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (zeroArm : ZeroRecipientTransferAndCallAllowanceArm dp ca)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransported ca checkpoint.state future.state
      history.attributionLedger :=
  AccountedHistory.allowanceTransported
    (committedExecAllowanceSound dp ca zeroArm) history hstable

end Weth10

end Blanc
