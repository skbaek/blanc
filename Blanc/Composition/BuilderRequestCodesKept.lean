import Blanc.Composition.RequestPhaseAmsterdam
import Blanc.ExecutionKeptChain

/-!
# The four request-contract codes persist along a kept history

Outcome O38 of `blanc-eip8282-builder-requests-v1` §19. From a start with all four
codes installed, at the end of every kept history those codes are still installed, so
O9's fold succeeds on the next block. Guarantee 2 in history form.

This lives in `Composition`, not in a contract family, because only it needs the
request-phase fold: `Lift` importing `Composition` would break layering.
-/

namespace Blanc.Composition.BuilderRequestCodesKept

open Jaune
open Blanc.Lift.BuilderRequest

/-- **The four codes persist along a kept history.** Each address keeps the
code it started with, needing only nonempty code and no delegation. -/
theorem codes_persist {cfg : ChainConfig} {start post : BlockChain}
    {blocks : List KeptBlock} (h : Blanc.KeptHistory cfg start blocks post)
    (h7002 : start.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode)
    (h7251 : start.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode)
    (hdep : start.state.getCode Deposit.Creation.address = Deposit.code)
    (hexit : start.state.getCode Exit.Creation.address = Exit.code)
    (ne7002 : (start.state.getCode withdrawalRequestPredeployAddress).toList ≠ [])
    (nd7002 : ¬ isValidDelegation (start.state.getCode withdrawalRequestPredeployAddress))
    (ne7251 : (start.state.getCode consolidationRequestPredeployAddress).toList ≠ [])
    (nd7251 : ¬ isValidDelegation (start.state.getCode consolidationRequestPredeployAddress))
    (nedep : (start.state.getCode Deposit.Creation.address).toList ≠ [])
    (nddep : ¬ isValidDelegation (start.state.getCode Deposit.Creation.address))
    (neexit : (start.state.getCode Exit.Creation.address).toList ≠ [])
    (ndexit : ¬ isValidDelegation (start.state.getCode Exit.Creation.address)) :
    post.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode ∧
    post.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode ∧
    post.state.getCode Deposit.Creation.address = Deposit.code ∧
    post.state.getCode Exit.Creation.address = Exit.code := by
  obtain ⟨-, c7002⟩ := h.chain ne7002 nd7002
  obtain ⟨-, c7251⟩ := h.chain ne7251 nd7251
  obtain ⟨-, cdep⟩ := h.chain nedep nddep
  obtain ⟨-, cexit⟩ := h.chain neexit ndexit
  exact ⟨c7002.trans h7002, c7251.trans h7251, cdep.trans hdep, cexit.trans hexit⟩

/-- **The next request pass cannot fail.** At any Amsterdam `benv` over the
post state, the four checked calls return and the fold over
`amsterdamRules.requests` succeeds. -/
theorem next_pass_succeeds {cfg : ChainConfig} {start post : BlockChain}
    {blocks : List KeptBlock} (h : Blanc.KeptHistory cfg start blocks post)
    (h7002 : start.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode)
    (h7251 : start.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode)
    (hdep : start.state.getCode Deposit.Creation.address = Deposit.code)
    (hexit : start.state.getCode Exit.Creation.address = Exit.code)
    (ne7002 : (start.state.getCode withdrawalRequestPredeployAddress).toList ≠ [])
    (nd7002 : ¬ isValidDelegation (start.state.getCode withdrawalRequestPredeployAddress))
    (ne7251 : (start.state.getCode consolidationRequestPredeployAddress).toList ≠ [])
    (nd7251 : ¬ isValidDelegation (start.state.getCode consolidationRequestPredeployAddress))
    (nedep : (start.state.getCode Deposit.Creation.address).toList ≠ [])
    (nddep : ¬ isValidDelegation (start.state.getCode Deposit.Creation.address))
    (neexit : (start.state.getCode Exit.Creation.address).toList ≠ [])
    (ndexit : ¬ isValidDelegation (start.state.getCode Exit.Creation.address))
    {benv : Benv} (hstate : benv.state = post.state)
    (hfork : benv.stat.fork = .amsterdam) (idx : Nat) (acc : List Bytes)
    (bal : BalBuilder) :
    ∃ (out1 out2 out3 out4 : MsgCallOutput) (bal' : BalBuilder),
      processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
        .ok (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals benv.state,
          out1) ∧
      processCheckedSystemTransaction
        (benv.withState
          (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals benv.state))
        consolidationRequestPredeployAddress [] =
        .ok (Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations
          (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals benv.state),
          out2) ∧
      processCheckedSystemTransaction
        (benv.withState
          (Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations
            (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals
              benv.state)))
        Deposit.Creation.address [] =
        .ok (Blanc.Composition.RequestPhaseAmsterdam.afterDeposits
          (Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations
            (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals
              benv.state)),
          out3) ∧
      processCheckedSystemTransaction
        (benv.withState
          (Blanc.Composition.RequestPhaseAmsterdam.afterDeposits
            (Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations
              (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals
                benv.state))))
        Exit.Creation.address [] =
        .ok (Blanc.Composition.RequestPhaseAmsterdam.afterExits
          (Blanc.Composition.RequestPhaseAmsterdam.afterDeposits
            (Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations
              (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals
                benv.state))),
          out4) ∧
      runRequestContracts idx amsterdamRules.requests benv acc bal =
        .ok (Blanc.Composition.RequestPhaseAmsterdam.afterExits
          (Blanc.Composition.RequestPhaseAmsterdam.afterDeposits
            (Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations
              (Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals
                benv.state))),
          acc ++ Blanc.ExecutionTrace.optionalRequestEntry 1 out1.returnData ++
            Blanc.ExecutionTrace.optionalRequestEntry 2 out2.returnData ++
            Blanc.ExecutionTrace.optionalRequestEntry 3 out3.returnData ++
            Blanc.ExecutionTrace.optionalRequestEntry 4 out4.returnData,
          bal') ∧
      benv.stat.rules.requests = amsterdamRules.requests := by
  have hp := codes_persist h h7002 h7251 hdep hexit ne7002 nd7002 ne7251 nd7251
    nedep nddep neexit ndexit
  rw [← hstate] at hp
  obtain ⟨p7002, p7251, pdep, pexit⟩ := hp
  exact Blanc.Composition.RequestPhaseAmsterdam.request_phase hfork p7002 p7251
    pdep pexit idx acc bal

end Blanc.Composition.BuilderRequestCodesKept
