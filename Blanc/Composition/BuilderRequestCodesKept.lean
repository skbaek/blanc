import Blanc.Composition.RequestPhaseAmsterdamBase
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

/-- **The four request contracts' code at a state.** One named bundle for the
code-installation premises the fold needs; each code is concrete, so nonemptiness
and no-delegation follow from these equalities and are not premises. -/
structure CodesAt (σ : State) : Prop where
  /-- EIP-7002's code is installed. -/
  w7002 : σ.getCode withdrawalRequestPredeployAddress =
    Blanc.withdrawalRequestCode
  /-- EIP-7251's code is installed. -/
  w7251 : σ.getCode consolidationRequestPredeployAddress =
    Blanc.consolidationRequestCode
  /-- The deposit code is installed. -/
  dep : σ.getCode Deposit.Creation.address = Deposit.code
  /-- The exit code is installed. -/
  ext : σ.getCode Exit.Creation.address = Exit.code

/-- **The four codes persist along a kept history.** Each address keeps the
code it started with; the codes are concrete, so nonemptiness and no-delegation
are derived from the equalities, not assumed. -/
theorem codes_persist {cfg : ChainConfig} {start post : BlockChain}
    {blocks : List KeptBlock} (h : Blanc.KeptHistory cfg start blocks post)
    (codes : CodesAt start.state) : CodesAt post.state := by
  have ne7002 : (start.state.getCode withdrawalRequestPredeployAddress).toList ≠ [] := by
    rw [codes.w7002]
    decide +kernel
  have nd7002 : ¬ isValidDelegation (start.state.getCode withdrawalRequestPredeployAddress) := by
    rw [codes.w7002]
    decide +kernel
  have ne7251 : (start.state.getCode consolidationRequestPredeployAddress).toList ≠ [] := by
    rw [codes.w7251]
    decide +kernel
  have nd7251 : ¬ isValidDelegation (start.state.getCode consolidationRequestPredeployAddress) := by
    rw [codes.w7251]
    decide +kernel
  have nedep : (start.state.getCode Deposit.Creation.address).toList ≠ [] := by
    rw [codes.dep]
    decide +kernel
  have nddep : ¬ isValidDelegation (start.state.getCode Deposit.Creation.address) := by
    rw [codes.dep]
    decide +kernel
  have neexit : (start.state.getCode Exit.Creation.address).toList ≠ [] := by
    rw [codes.ext]
    decide +kernel
  have ndexit : ¬ isValidDelegation (start.state.getCode Exit.Creation.address) := by
    rw [codes.ext]
    decide +kernel
  obtain ⟨-, c7002⟩ := h.chain ne7002 nd7002
  obtain ⟨-, c7251⟩ := h.chain ne7251 nd7251
  obtain ⟨-, cdep⟩ := h.chain nedep nddep
  obtain ⟨-, cexit⟩ := h.chain neexit ndexit
  exact ⟨c7002.trans codes.w7002, c7251.trans codes.w7251, cdep.trans codes.dep,
    cexit.trans codes.ext⟩

/-- **The next request pass cannot fail.** At any Amsterdam `benv` over the
post state, the four checked calls return and the fold over
`amsterdamRules.requests` succeeds. -/
theorem next_pass_succeeds {cfg : ChainConfig} {start post : BlockChain}
    {blocks : List KeptBlock} (h : Blanc.KeptHistory cfg start blocks post)
    (codes : CodesAt start.state)
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
  have hp := codes_persist h codes
  rw [← hstate] at hp
  obtain ⟨p7002, p7251, pdep, pexit⟩ := hp
  exact Blanc.Composition.RequestPhaseAmsterdam.request_phase hfork p7002 p7251
    pdep pexit idx acc bal

end Blanc.Composition.BuilderRequestCodesKept
