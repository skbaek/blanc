import Blanc.Lift.BuilderRequest.Deposit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Deposit.Revert
import Blanc.Lift.BuilderRequest.Exit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Exit.Revert
import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.BuilderRequest.Delivery
import Blanc.Lift.BuilderRequest.FeePath
import Blanc.Lift.BuilderRequest.FeeRead
import Blanc.Lift.BuilderRequest.SystemOutput
import Blanc.RequestFeeWordDomain

/-!
# What the builder contracts accept, and the unlock quote

Outcomes O33 and O34 of `blanc-eip8282-builder-requests-v1` §19, under
`fork = .amsterdam`. O38 lives in `Blanc.Composition.BuilderRequestCodesKept`,
since only it needs the request-phase fold.

O33 states what each contract accepts, from the existing Submission and Revert
laws: the forward direction is the Submission law applied verbatim, the reverse
is the Revert law. O34 states that an inhibited system call resets the fee:
the clearing step is storage-level (`drainStor` with `excessNext_inhibitor`), so
no `Holds` premise is needed, and a fee read on the cleared storage quotes
`fakeExp 1 0 17`.
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

/-- **An inhibited SYSTEM-gated deposit call clears excess and count.** The post state
is `drainStor`, whose slots 0 and 1 are 0 on the inhibitor; a finding about the EIP text's
"permanently", reachable only on the system path, not an attack. -/
theorem deposit_unlock_clears {benv : Benv} {post : State} {result : MsgCallOutput}
    (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode Deposit.Creation.address = Deposit.code)
    (inhibited : (benv.state.getStor Deposit.Creation.address).get 0 = B256.max)
    (run : processCheckedSystemTransaction benv Deposit.Creation.address [] =
      .ok (post, result)) :
    (post.getStor Deposit.Creation.address).get 0 = 0 ∧
      (post.getStor Deposit.Creation.address).get 1 = 0 := by
  obtain ⟨hpost, -⟩ := Deposit.system_law hfork installed run
  have hn : Deposit.sysShape.next = excessNext Deposit.sysShape.target.word :=
    Deposit.contract.next_eq
  constructor
  · rw [hpost, RequestSystem.sysState_get_zero, hn, inhibited]
    exact excessNext_inhibitor _ _
  · rw [hpost, RequestSystem.sysState_get, ite_eq_left (show (1 : B256) = 1 from rfl)]

/-- **An inhibited SYSTEM-gated exit call clears excess and count.** The post state
is `drainStor`, whose slots 0 and 1 are 0 on the inhibitor; a finding about the EIP text's
"permanently", reachable only on the system path, not an attack. -/
theorem exit_unlock_clears {benv : Benv} {post : State} {result : MsgCallOutput}
    (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode Exit.Creation.address = Exit.code)
    (inhibited : (benv.state.getStor Exit.Creation.address).get 0 = B256.max)
    (run : processCheckedSystemTransaction benv Exit.Creation.address [] =
      .ok (post, result)) :
    (post.getStor Exit.Creation.address).get 0 = 0 ∧
      (post.getStor Exit.Creation.address).get 1 = 0 := by
  obtain ⟨hpost, -⟩ := Exit.system_law hfork installed run
  have hn : Exit.sysShape.next = excessNext Exit.sysShape.target.word :=
    Exit.contract.next_eq
  constructor
  · rw [hpost, RequestSystem.sysState_get_zero, hn, inhibited]
    exact excessNext_inhibitor _ _
  · rw [hpost, RequestSystem.sysState_get, ite_eq_left (show (1 : B256) = 1 from rfl)]

/-- The quote on cleared storage is `fakeExp 1 0 17`, from the cleared excess. -/
private theorem quote_of_cleared {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}
    {target : B256} {iterations : Nat} {finalOutput : B256}
    (read : UserPath.FeeReadOn l target pre post iterations finalOutput)
    (hsum : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat) < 2 ^ 256)
    (hle : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat) ≤ 2892)
    (hclear : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - target.toNat) = 0) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 0 17 := by
  have hq := read.fee_eq_natural hsum hle
  rw [hclear] at hq
  exact hq

/-- **After the deposit unlock the quote is `fakeExp 1 0 17`.** On cleared
storage the quoted excess is 0, inside the no-wrap domain; a SYSTEM-gated finding about
the EIP text, whatever the backlog, not an attack. -/
theorem deposit_unlock_quote {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}
    {iterations : Nat} {finalOutput : B256}
    (read : UserPath.FeeReadOn l 8 pre post iterations finalOutput)
    (h0 : pre.getStorVal sevm.currentTarget 0 = 0)
    (h1 : pre.getStorVal sevm.currentTarget 1 = 0) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 0 17 := by
  have h8 : (8 : B256).toNat = 8 := by decide
  have hsum : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - (8 : B256).toNat) < 2 ^ 256 := by
    rw [h0, h1, h8]
    decide
  have hle : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - (8 : B256).toNat) ≤ 2892 := by
    rw [h0, h1, h8]
    decide
  have hclear : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - (8 : B256).toNat) = 0 := by
    rw [h0, h1, h8]
    decide
  exact quote_of_cleared read hsum hle hclear

/-- **After the exit unlock the quote is `fakeExp 1 0 17`.** On cleared
storage the quoted excess is 0, inside the no-wrap domain; a SYSTEM-gated finding about
the EIP text, whatever the backlog, not an attack. -/
theorem exit_unlock_quote {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}
    {iterations : Nat} {finalOutput : B256}
    (read : UserPath.FeeReadOn l 2 pre post iterations finalOutput)
    (h0 : pre.getStorVal sevm.currentTarget 0 = 0)
    (h1 : pre.getStorVal sevm.currentTarget 1 = 0) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 0 17 := by
  have h2 : (2 : B256).toNat = 2 := by decide
  have hsum : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - (2 : B256).toNat) < 2 ^ 256 := by
    rw [h0, h1, h2]
    decide
  have hle : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - (2 : B256).toNat) ≤ 2892 := by
    rw [h0, h1, h2]
    decide
  have hclear : (pre.getStorVal sevm.currentTarget 0).toNat +
      ((pre.getStorVal sevm.currentTarget 1).toNat - (2 : B256).toNat) = 0 := by
    rw [h0, h1, h2]
    decide
  exact quote_of_cleared read hsum hle hclear

end Blanc.Lift.BuilderRequest
