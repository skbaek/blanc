import Blanc.Lift.BuilderRequest.Deposit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Deposit.Revert
import Blanc.Lift.BuilderRequest.Exit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Exit.Revert
import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.BuilderRequest.Delivery
import Blanc.Lift.BuilderRequest.FeePath
import Blanc.Lift.BuilderRequest.SystemOutput
import Blanc.RequestFeeWordDomain
import Blanc.ExecutionKeptChain
import Blanc.Composition.RequestPhaseAmsterdam

/-!
# What the builder contracts accept, the unlock quote, and the next pass

Outcomes O33, O34 and O38 of `blanc-eip8282-builder-requests-v1` §19, under
`fork = .amsterdam`. O31 and O32 belong to another run and are not stated here;
there is no public layer in this file.

O33 states what each contract accepts, from the existing Submission and Revert
laws: the forward direction is the Submission law applied verbatim, the reverse
is the Revert law. O34 states that an inhibited system call resets the fee:
the clearing step is storage-level (`drainStor` with `excessNext_inhibitor`), so
no `Holds` premise is needed, and a fee read on the cleared storage quotes
`fakeExp 1 0 17`. O38 states that the four codes persist along a kept history,
so `request_phase` applies at the post state and the next request pass succeeds.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-! ## O33: what the contracts accept -/

/-- **The deposit contract accepts any passing 184-byte payload.** The guards'
`Admitted` mentions only the amount lane (calldata bytes 80 to 87, big-endian)
and value versus fee: pubkey, credentials and signature are unconstrained. -/
theorem deposit_accepts {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat}
    {finalOutput : B256} (hcode : sevm.code = Deposit.code)
    (hfork : sevm.benvStat.fork = .amsterdam) (caller : sevm.caller ≠ systemAddress)
    (hlen : sevm.data.length = 184) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations
      finalOutput)
    (admitted : Deposit.Admitted sevm (finalOutput / (17 : B256))) :
    Nonempty (Exec 0 sevm (St b [] M (G + Deposit.submissionGasA sevm b M iterations))
      (.ok (Deposit.submissionPostA sevm (Deposit.feeBaseA sevm b) M
        (G + Deposit.submissionRepayA sevm b M)))) :=
  Deposit.exec_submission_exact_amsterdam hcode hfork caller hlen dynamic slack off
    wordRun admitted

/-- **A non-passing deposit submission reverts.** With 184 bytes of calldata off
the inhibitor, `¬ Admits` is exactly the guards' rejection. -/
theorem deposit_rejects {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = Deposit.code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 184)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (rejected : ¬ Deposit.Admits s.data s.value (out / (17 : B256))) :
    FrameReverts s b (revertBound n) :=
  Deposit.frameReverts_not_admitted hcode hfork caller hlen off wordRun rejected

/-- **The exit contract accepts any funded 48-byte payload.** The guard is only
value covering the fee, so any caller queues an exit for any pubkey. -/
theorem exit_accepts {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat}
    {finalOutput : B256} (hcode : sevm.code = Exit.code)
    (hfork : sevm.benvStat.fork = .amsterdam) (caller : sevm.caller ≠ systemAddress)
    (hlen : sevm.data.length = 48) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations
      finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] M (G + Exit.submissionGasA sevm b M iterations))
      (.ok (Exit.submissionPostA sevm (Exit.feeBaseA sevm b) M
        (G + Exit.submissionRepayA sevm b M)))) :=
  Exit.exec_submission_amsterdam hcode hfork caller hlen dynamic slack off wordRun
    cov

/-- **An underfunded exit submission reverts.** With 48 bytes of calldata off
the inhibitor, value below the quoted fee is exactly the guard's rejection. -/
theorem exit_rejects {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = Exit.code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 48)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (rejected : ¬ Exit.Admits s.data s.value (out / (17 : B256))) :
    FrameReverts s b (revertBound n) :=
  Exit.frameReverts_not_admitted hcode hfork caller hlen off wordRun rejected

/-- **A plain value transfer to the deposit contract reverts.** Empty calldata
with nonzero value is a paid fee read. -/
theorem deposit_transfer_reverts {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = Deposit.code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (empty : s.data = []) (paid : s.value ≠ 0) :
    FrameReverts s b (revertBound n) :=
  Deposit.frameReverts_paidRead hcode hfork caller off wordRun empty paid

/-- **A plain value transfer to the exit contract reverts.** Empty calldata
with nonzero value is a paid fee read. -/
theorem exit_transfer_reverts {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = Exit.code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (empty : s.data = []) (paid : s.value ≠ 0) :
    FrameReverts s b (revertBound n) :=
  Exit.frameReverts_paidRead hcode hfork caller off wordRun empty paid

/-! ## O34: the unlock resets the fee -/

/-- **An inhibited deposit system call clears excess and count.** The post state
is `drainStor`, whose slots 0 and 1 are 0 on the inhibitor. -/
theorem deposit_unlock_clears {benv : Benv} {post : State} {result : MsgCallOutput}
    (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode Deposit.Creation.address = Deposit.code)
    (inhibited : (benv.state.getStor Deposit.Creation.address).get 0 = B256.max)
    (run : processCheckedSystemTransaction benv Deposit.Creation.address [] =
      .ok (post, result)) :
    (post.getStor Deposit.Creation.address).get 0 = 0 ∧
      (post.getStor Deposit.Creation.address).get 1 = 0 := by
  -- DRAFT: from `Deposit.contract.system_law` the post state is `sysState`; rewrite with
  -- `Delivery.sysState_getStor` to `Delivery.drainStor`; slot 1 is the outer `set 1 0`,
  -- slot 0 is `Deposit.contract.next_eq` with `Deposit.contract.target_eq` closed by
  -- `SystemOutput.excessNext_inhibitor` at the inhibited slot 0.
  sorry

/-- **An inhibited exit system call clears excess and count.** The post state
is `drainStor`, whose slots 0 and 1 are 0 on the inhibitor. -/
theorem exit_unlock_clears {benv : Benv} {post : State} {result : MsgCallOutput}
    (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode Exit.Creation.address = Exit.code)
    (inhibited : (benv.state.getStor Exit.Creation.address).get 0 = B256.max)
    (run : processCheckedSystemTransaction benv Exit.Creation.address [] =
      .ok (post, result)) :
    (post.getStor Exit.Creation.address).get 0 = 0 ∧
      (post.getStor Exit.Creation.address).get 1 = 0 := by
  -- DRAFT: as `deposit_unlock_clears`, with `Exit.contract` (`target_eq` is 2, `next_eq`
  -- the same `excessNext` shape) and `Delivery.latchStor` not needed since data is empty.
  sorry

/-- **After the deposit unlock the quote is `fakeExp 1 0 17`.** On cleared
storage the quoted excess is 0, inside the no-wrap domain. -/
theorem deposit_unlock_quote {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}
    {iterations : Nat} {finalOutput : B256}
    (read : UserPath.FeeReadOn l 8 pre post iterations finalOutput)
    (h0 : pre.getStorVal sevm.currentTarget 0 = 0)
    (h1 : pre.getStorVal sevm.currentTarget 1 = 0) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 0 17 := by
  -- DRAFT: `read.quote` runs on `storedExcess 8 sevm pre`, which is
  -- `FeePath.targetExcess 8 0 0 = 0` by `h0`, `h1` (`¬ (8 : B256) < 0`, then
  -- `targetExcess_toNat`); close with `Blanc.RequestFeeWord.word_fee_eq_natural`
  -- at `0 ≤ 2892`. `fakeExp 1 0 17 = 1` is left for the master (`by decide`).
  sorry

/-- **After the exit unlock the quote is `fakeExp 1 0 17`.** On cleared
storage the quoted excess is 0, inside the no-wrap domain. -/
theorem exit_unlock_quote {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}
    {iterations : Nat} {finalOutput : B256}
    (read : UserPath.FeeReadOn l 2 pre post iterations finalOutput)
    (h0 : pre.getStorVal sevm.currentTarget 0 = 0)
    (h1 : pre.getStorVal sevm.currentTarget 1 = 0) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 0 17 := by
  -- DRAFT: as `deposit_unlock_quote`, with target `2` (`¬ (2 : B256) < 0`).
  sorry

/-! ## O38: the next pass cannot fail along a history -/

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
  -- DRAFT: `Blanc.KeptHistory.chain` once per address gives
  -- `post.state.getCode a = start.state.getCode a`; rewrite with the four `h*`.
  -- The `ne*`/`nd*` for the builder contracts are `Deposit.linked.runnable` and
  -- `Exit.linked.runnable` (`by decide +kernel`); the EIP-7002/7251 pair stays premises.
  sorry

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
  -- DRAFT: subst `hstate`; get the four post-state installations from `codes_persist`;
  -- then this is `Blanc.Composition.RequestPhaseAmsterdam.request_phase` at `benv`.
  sorry

end Blanc.Lift.BuilderRequest
