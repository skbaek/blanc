import Blanc.DripRealizedExec
import Blanc.ExecutionAccountingLadder

namespace Blanc
open Jaune
namespace Drip

/-- DRIP's realized accounting as an `AccountingLadder` over the storage-only
`dripSpec`.  `dripSpec.Side` is `True`, so the root replay rebuilds the
balance-side `dripEntrySpec` readiness from the word bound the ladder threads. -/
noncomputable def ladder (coalition : Finset Adr) (ca : Adr) :
    ExecutionAccountingReplay.AccountingLadder dripSpec ca where
  carrier := carrier coalition ca
  append := fun first second => Chain.append first second
  tag _ _ := ()
  root := by
    intro _ _ msg entry pc sevm pre out run transfer evmEq committed runReady
      callerNe hfork sumNof
    exact (_root_.Blanc.Exec.dripRealizedChain_of_messageRoot coalition run
      transfer evmEq committed (dripEntrySpec_messageRunReady runReady sumNof)
      callerNe hfork).imp fun _ both => both.1
  preserves := dripSpec_preserves ca

/-- T4c. -/
theorem retainedMessageCallReplay (coalition : Finset Adr)
    {ca : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : ExecutionTrace.MessageCallTrace msg state out)
    (ready : dripSpec.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork msg.benv.stat.fork) :
    ∃ steps, RealizedChain (snapshot coalition ca msg.benv.state) steps
      (snapshot coalition ca state) :=
  (ladder coalition ca).messageCall trace ready callerNe sumNof hfork 0 none

/-- T11. -/
theorem retainedConfiguredHistoryReplay (coalition : Finset Adr)
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (inv : dripSpec.StateInv ca checkpoint.state)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, RealizedChain (snapshot coalition ca checkpoint.state) steps
      (snapshot coalition ca future.state) :=
  (ladder coalition ca).configuredHistory history inv hcov

end Drip
end Blanc
