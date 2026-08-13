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

The same partition is then run a second time against the read-sound arms,
producing `CompiledFrameAllowanceReadHandler` and, downstream of it,
`AccountedHistory.allowanceTransportedSound_of_compiled`.  That second pass is
a sibling of the first, not a replacement: the endpoints pinned by type keep
their exact statements and are recovered from the read-sound siblings by the
generic downgrades.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Thirty-way selector dispatch

The balance partition classifies `transfer` by its recipient argument
(`CallFreeStorageBranch.transferNonzero` versus
`RemainingStorageBranch.transferZero`) but classifies `transferAndCall` by
selector alone: its `RemainingStorageBranch.transferAndCall` leaf carries no
recipient datum.  The balance arm needs none, because
`hasProofIndexedStorageAccounting_of_transferAndCall` covers both recipients;
the allowance development instead supplies two arms for that leaf, one per
recipient, and splits on the recipient word here. -/

/-- Exact allowance-region handler for every authentic compiled WETH10 frame.
Every selector arm is discharged by its concrete chronology; the selector case
split is the balance development's already-proved partition. -/
theorem compiledFrameAllowanceHandler (dp : DeployParams) (ca : Adr) :
    CompiledFrameAllowanceHandler dp ca := by
  intro frame context hdeeper
  rcases Blanc.Weth10.Exec.Frame.callFreeStorageBranch_or_remaining (frame := frame) context with
      closed | openCase
  · cases closed with
    | receive empty =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_receive (frame := frame) context empty
    | deposit nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_deposit (frame := frame) context selected nonempty
    | depositTo nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_depositTo (frame := frame) context selected nonempty
    | transferNonzero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_transferNonzero (frame := frame)
          context selected nonempty recipient
    | transferFromNonzero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_transferFromNonzero (frame := frame)
          context selected nonempty recipient
    | noFlow branch =>
        cases branch with
        | name nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_name (frame := frame)
              context selected nonempty
        | approve nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_approve (frame := frame)
              context selected nonempty
        | totalSupply nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_totalSupply (frame := frame)
              context selected nonempty
        | permitTypehash nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_permitTypehash (frame := frame)
              context selected nonempty
        | decimals nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_decimals (frame := frame)
              context selected nonempty
        | domainSeparator nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_domainSeparator (frame := frame)
              context selected nonempty
        | maxFlashLoan nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_maxFlashLoan (frame := frame)
              context selected nonempty
        | balanceOf nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_balanceOf (frame := frame)
              context selected nonempty
        | nonces nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_nonces (frame := frame)
              context selected nonempty
        | callbackSuccess nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_callbackSuccess (frame := frame)
              context selected nonempty
        | flashMinted nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_flashMinted (frame := frame)
              context selected nonempty
        | symbol nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_symbol (frame := frame)
              context selected nonempty
        | deploymentChainId nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_deploymentChainId (frame := frame)
              context selected nonempty
        | flashFee nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_flashFee (frame := frame)
              context selected nonempty
        | allowance nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_allowance (frame := frame)
              context selected nonempty
  · cases openCase with
    | depositToAndCall nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_depositToAndCall (frame := frame)
          context selected nonempty hdeeper
    | transferZero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_transferZero (frame := frame)
          context selected nonempty recipient hdeeper
    | transferAndCall nonempty selected =>
        by_cases hzero : Sevm.argWord frame.sevm 0 = 0
        · exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_transferAndCallZero (frame := frame)
            context selected nonempty hzero hdeeper
        · exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_transferAndCall (frame := frame)
            context selected nonempty hzero hdeeper
    | transferFromZero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_transferFromZero (frame := frame)
          context selected nonempty recipient hdeeper
    | withdraw nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_withdraw (frame := frame)
          context selected nonempty hdeeper
    | withdrawTo nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_withdrawTo (frame := frame)
          context selected nonempty hdeeper
    | withdrawFrom nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_withdrawFrom (frame := frame)
          context selected nonempty hdeeper
    | flashLoan nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_flashLoan (frame := frame)
          context selected nonempty hdeeper
    | approveAndCall nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_approveAndCall (frame := frame)
          context selected nonempty hdeeper
    | permit nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffect_of_permit (frame := frame)
          context selected nonempty hdeeper

/-! ## Lift to the history level -/

/-- Compiled-program allowance handler consumed by the generic recursion. -/
theorem compiledBodyAllowanceHandler (dp : DeployParams) (ca : Adr) :
    CompiledBodyAllowanceHandler dp ca :=
  (compiledFrameAllowanceHandler dp ca).compiledBodyAllowanceHandler

/-- Complete committed allowance accounting for the installed WETH10
program. -/
theorem committedExecAllowanceSound (dp : DeployParams) (ca : Adr) :
    CommittedExecAllowanceSound dp ca :=
  CompiledBodyAllowanceHandler.committedExecAllowanceSound
    (compiledBodyAllowanceHandler dp ca)

/-- Every tagged allowance key of an authentic stable-root history holds
exactly the last committed write recorded by the history's chronological
attribution ledger, or its checkpoint value when no counted write touches it.
Downstream consumers supply only the history and its stable checkpoint. -/
theorem AccountedHistory.allowanceTransported_of_compiled
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransported ca checkpoint.state future.state
      history.attributionLedger :=
  AccountedHistory.allowanceTransported
    (committedExecAllowanceSound dp ca) history hstable

/-! ## The read-sound dispatch

The same thirty-one-way case split, run against the read-sound arms.  It is a
sibling of the development above rather than a replacement for it: the landed
`compiledFrameAllowanceHandler` and everything downstream of it keep their
exact statements, so no published claim silently changes what it asserts.

The two developments cannot share a dispatcher.  The recursion hypothesis
`ForallDeeperAt … Exec.CoreAllowanceReadSound` occurs to the left of an
arrow, so the landed handler — which is handed only the weaker
`Exec.CoreAllowanceSound` at that position — cannot feed the read-sound arms,
and the case split has to be transcribed rather than reused. -/

/-- Read-sound allowance-region handler for every authentic compiled WETH10
frame: each selector arm additionally certifies that the records it
contributes read `ca`'s frame-entry allowance word.  The selector case split
is the balance development's already-proved partition, exactly as in
`compiledFrameAllowanceHandler`. -/
theorem compiledFrameAllowanceHandlerSound (dp : DeployParams) (ca : Adr) :
    CompiledFrameAllowanceReadHandler dp ca := by
  intro frame context hdeeper
  rcases Blanc.Weth10.Exec.Frame.callFreeStorageBranch_or_remaining (frame := frame) context with
      closed | openCase
  · cases closed with
    | receive empty =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_receive (frame := frame) context empty
    | deposit nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_deposit (frame := frame) context selected
          nonempty
    | depositTo nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_depositTo (frame := frame) context selected
          nonempty
    | transferNonzero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_transferNonzero (frame := frame)
          context selected nonempty recipient
    | transferFromNonzero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_transferFromNonzero (frame := frame)
          context selected nonempty recipient
    | noFlow branch =>
        cases branch with
        | name nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_name (frame := frame)
              context selected nonempty
        | approve nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_approve (frame := frame)
              context selected nonempty
        | totalSupply nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_totalSupply (frame := frame)
              context selected nonempty
        | permitTypehash nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_permitTypehash (frame := frame)
              context selected nonempty
        | decimals nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_decimals (frame := frame)
              context selected nonempty
        | domainSeparator nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_domainSeparator (frame := frame)
              context selected nonempty
        | maxFlashLoan nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_maxFlashLoan (frame := frame)
              context selected nonempty
        | balanceOf nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_balanceOf (frame := frame)
              context selected nonempty
        | nonces nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_nonces (frame := frame)
              context selected nonempty
        | callbackSuccess nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_callbackSuccess (frame := frame)
              context selected nonempty
        | flashMinted nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_flashMinted (frame := frame)
              context selected nonempty
        | symbol nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_symbol (frame := frame)
              context selected nonempty
        | deploymentChainId nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_deploymentChainId (frame := frame)
              context selected nonempty
        | flashFee nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_flashFee (frame := frame)
              context selected nonempty
        | allowance nonempty selected =>
            exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_allowance (frame := frame)
              context selected nonempty
  · cases openCase with
    | depositToAndCall nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_depositToAndCall (frame := frame)
          context selected nonempty hdeeper
    | transferZero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_transferZero (frame := frame)
          context selected nonempty recipient hdeeper
    | transferAndCall nonempty selected =>
        by_cases hzero : Sevm.argWord frame.sevm 0 = 0
        · exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_transferAndCallZero (frame := frame)
            context selected nonempty hzero hdeeper
        · exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_transferAndCall (frame := frame)
            context selected nonempty hzero hdeeper
    | transferFromZero nonempty selected recipient =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_transferFromZero (frame := frame)
          context selected nonempty recipient hdeeper
    | withdraw nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_withdraw (frame := frame)
          context selected nonempty hdeeper
    | withdrawTo nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_withdrawTo (frame := frame)
          context selected nonempty hdeeper
    | withdrawFrom nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_withdrawFrom (frame := frame)
          context selected nonempty hdeeper
    | flashLoan nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_flashLoan (frame := frame)
          context selected nonempty hdeeper
    | approveAndCall nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_approveAndCall (frame := frame)
          context selected nonempty hdeeper
    | permit nonempty selected =>
        exact Blanc.Weth10.Exec.Frame.allowanceRegionEffectSound_of_permit (frame := frame)
          context selected nonempty hdeeper

/-! ## Lift the read-sound dispatch to the history level -/

/-- Read-sound compiled-program allowance handler consumed by the generic
recursion. -/
theorem compiledBodyAllowanceHandlerSound (dp : DeployParams) (ca : Adr) :
    CompiledBodyAllowanceReadHandler dp ca :=
  (compiledFrameAllowanceHandlerSound dp ca).compiledBodyAllowanceReadHandler

/-- Complete read-sound committed allowance accounting for the installed
WETH10 program: the settled transport of the landed obligation, plus entry-read
soundness of the same attribution stream against the same entry storage. -/
theorem committedExecAllowanceReadSound (dp : DeployParams) (ca : Adr) :
    CommittedExecAllowanceReadSound dp ca :=
  CompiledBodyAllowanceReadHandler.committedExecAllowanceReadSound
    (compiledBodyAllowanceHandlerSound dp ca)

/-- Every tagged allowance key of an authentic stable-root history holds
exactly the last committed write recorded by the history's chronological
attribution ledger, or its checkpoint value when no counted write touches it —
and every allowance event in that ledger was read from the storage the ledger
replays from.  Downstream consumers supply only the history and its stable
checkpoint. -/
theorem AccountedHistory.allowanceTransportedSound_of_compiled
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransportedSound ca checkpoint.state future.state
      history.attributionLedger :=
  AccountedHistory.allowanceTransportedSound
    (committedExecAllowanceReadSound dp ca) history hstable

/-! ## The read-sound siblings really do strengthen the landed endpoints

Both pinned endpoints are recovered from their `Sound` sibling by the generic
downgrades, so the sibling asserts everything the pinned statement asserts and
the pinned statements themselves never change. -/

example (dp : DeployParams) (ca : Adr) : CommittedExecAllowanceSound dp ca :=
  CommittedExecAllowanceReadSound.committedExecAllowanceSound
    (committedExecAllowanceReadSound dp ca)

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransported ca checkpoint.state future.state
      history.attributionLedger :=
  (history.allowanceTransportedSound_of_compiled hstable).toAllowanceTransported

end Weth10

end Blanc
