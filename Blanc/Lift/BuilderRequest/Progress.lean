import Blanc.Lift.BuilderRequest.Deposit.Frames
import Blanc.Lift.BuilderRequest.Deposit.Submission
import Blanc.Lift.BuilderRequest.Deposit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Exit.Frames
import Blanc.Lift.BuilderRequest.Exit.Submission
import Blanc.Lift.BuilderRequest.Exit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.UserFrameAmsterdam
import Blanc.Lift.BuilderRequest.FeePath
import Blanc.Lift.BuilderRequest.Latch
import Blanc.Lift.BuilderRequest.Deposit.Latch
import Blanc.Lift.BuilderRequest.Exit.Latch
import Blanc.Lift.BuilderRequest.Deposit.System
import Blanc.Lift.BuilderRequest.Exit.System
import Blanc.Lift.RequestSystem.Effects

/-!
# Progress for a frame at either builder code (O36)

Outcome O36 of `blanc-eip8282-builder-requests-v1` §19: a frame at either code with stated gas and
value succeeds, at frame level. Not a walk of a parent's code: every statement here is an `Exec` from
a `St` base, with no caller-side `CALL` walk.

**Caller analysis.** The bytes dispatch on `CALLER = SYSTEM_ADDRESS`: any other caller takes the user
arm (submission or fee read), `SYSTEM_ADDRESS` takes the system arm (drain, or the latch on nonempty
calldata). So "whatever its caller" splits by arm, and each arm states its own gas: the user arm
takes the submission/fee-read charge, the system arm the drain/latch charge. A single uniform gas
would need a gas-padding lemma (the same success at more gas, with a different post state), which no
shared module states; that lemma is open, so the arms stay separate. The user arms are proved below
at both forks, and the Amsterdam system arms via `latch_frame_run` and `frame_exec`. At covered forks
there is no SYSTEM-caller theorem: the protocol issues no system call before Amsterdam, and the drain
walk does not generalize within budget (see the covered system-arm section).

**Value.** A submission states the value its guards admit (deposit: `Admitted`, covering credit plus
fee; exit: value covering the fee); a fee read states zero value. The system arms take any value: the
drain and latch never check it.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-! ## Deposit, user arm -/

/-- **Deposit submission progress, under covered forks, for a non-system caller.** -/
theorem progress_submission_covered {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Deposit.code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 184)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput)
    (admitted : Deposit.Admitted sevm (finalOutput / (17 : B256))) :
    Nonempty (Exec 0 sevm (St b [] M (G + Deposit.submissionGas sevm b M iterations))
      (.ok (Deposit.submissionPost sevm (feeBase sevm b) M G))) :=
  Deposit.exec_submission_exact hcode fork caller hlen dynamic slack off wordRun admitted

/-- **Deposit fee-read progress, under covered forks, for a non-system caller.** -/
theorem progress_feeread_covered {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Deposit.code) (fork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase sevm b) M (finalOutput / (17 : B256)) G))) :=
  Deposit.exec_fee_read_exact hcode fork aligned caller empty zero off wordRun

/-- **Deposit submission progress, under Amsterdam.** -/
theorem progress_submission_amsterdam {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Deposit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 184)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput)
    (admitted : Deposit.Admitted sevm (finalOutput / (17 : B256))) :
    Nonempty (Exec 0 sevm (St b [] M (G + Deposit.submissionGasA sevm b M iterations))
      (.ok (Deposit.submissionPostA sevm (Deposit.feeBaseA sevm b) M
        (G + Deposit.submissionRepayA sevm b M)))) :=
  Deposit.exec_submission_exact_amsterdam hcode hfork caller hlen dynamic slack off wordRun admitted

/-- **Deposit fee-read progress, under Amsterdam.** -/
theorem progress_feeread_amsterdam {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Deposit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (aligned : M.size % 32 = 0) (wf : Mem.Wf M) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput) :
    ∃ post, Nonempty (Exec 0 sevm
        (St b [] M (G + UserPath.feeReadGasOn (amsterdamSteps sevm) b M iterations)) (.ok post)) ∧
      post.output = (finalOutput / (17 : B256)).toBytes ∧
      (∀ a, post.getStor a = b.getStor a) ∧ (∀ a, post.getBal a = b.getBal a) ∧ post.logs = b.logs :=
  Deposit.exec_fee_read_amsterdam hcode hfork aligned wf caller empty zero off wordRun

/-! ## Exit, user arm -/

/-- **Exit submission progress, under covered forks, for a non-system caller.** -/
theorem progress_submission_covered_exit {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Exit.code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 48)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] M (G + Exit.submissionGas sevm b M iterations))
      (.ok (Exit.submissionPost sevm (feeBase sevm b) M G))) :=
  Exit.exec_submission_exact hcode fork caller hlen dynamic slack off wordRun cov

/-- **Exit fee-read progress, under covered forks, for a non-system caller.** -/
theorem progress_feeread_covered_exit {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Exit.code) (fork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase sevm b) M (finalOutput / (17 : B256)) G))) :=
  Exit.exec_fee_read_exact hcode fork aligned caller empty zero off wordRun

/-- **Exit submission progress, under Amsterdam.** -/
theorem progress_submission_amsterdam_exit {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Exit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 48)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] M (G + Exit.submissionGasA sevm b M iterations))
      (.ok (Exit.submissionPostA sevm (Exit.feeBaseA sevm b) M
        (G + Exit.submissionRepayA sevm b M)))) :=
  Exit.exec_submission_amsterdam hcode hfork caller hlen dynamic slack off wordRun cov

/-- **Exit fee-read progress, under Amsterdam.** -/
theorem progress_feeread_amsterdam_exit {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Exit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (aligned : M.size % 32 = 0) (wf : Mem.Wf M) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput) :
    ∃ post, Nonempty (Exec 0 sevm
        (St b [] M (G + UserPath.feeReadGasOn (amsterdamSteps sevm) b M iterations)) (.ok post)) ∧
      post.output = (finalOutput / (17 : B256)).toBytes ∧
      (∀ a, post.getStor a = b.getStor a) ∧ (∀ a, post.getBal a = b.getBal a) ∧ post.logs = b.logs :=
  Exit.exec_fee_read_amsterdam hcode hfork aligned wf caller empty zero off wordRun

/-! ## System arm, under Amsterdam -/

/-- **A system-caller frame with nonempty calldata succeeds at the deposit code, under Amsterdam.** -/
theorem progress_system_submission_amsterdam {sevm : Sevm} {b : Devm} {G : Nat}
    (hcode : sevm.code = Deposit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress)
    (hne : sevm.data ≠ []) (hlen : sevm.data.length < 2 ^ 256)
    (p : LatchWords) (tree : Deposit.sysPath.shape.excessTree = sysExcess p)
    (len : p.len = Deposit.sysPath.shape.len)
    (r : Ready sevm b [2, 3, 0, 1]) (hG : gCallStipend < G) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] .empty (G + latchCost Deposit.sysPath sevm b))
      (.ok post)) := by
  have hdata : sevm.data.length.toB256 ≠ 0 := data_length_ne hne hlen
  have run := latch_frame_run Deposit.sysPath p tree len hfork hstatic hcaller hdata r hG
  exact ⟨_, lift_exact_noExec Deposit.sysPath.check Deposit.sysPath.jumps hcode
    Deposit.sysPath.noExec ⟨_, Deposit.sysPath.root, run⟩⟩

/-- **A system-caller frame with empty calldata succeeds at the deposit code, under Amsterdam.** -/
theorem progress_system_empty_amsterdam {sevm : Sevm} {b : Devm} {G : Nat}
    (hcode : sevm.code = Deposit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (r : Ready sevm b [2, 3, 0, 1]) (hG : gCallStipend < G) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] .empty (G + RequestSystem.SysPath.frameCost Deposit.sysPath sevm b))
      (.ok post)) :=
  ⟨_, RequestSystem.SysPath.frame_exec Deposit.sysPath hcode hfork hstatic hcaller hdata r hG⟩

/-- **A system-caller frame with nonempty calldata succeeds at the exit code, under Amsterdam.** -/
theorem progress_system_submission_amsterdam_exit {sevm : Sevm} {b : Devm} {G : Nat}
    (hcode : sevm.code = Exit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress)
    (hne : sevm.data ≠ []) (hlen : sevm.data.length < 2 ^ 256)
    (p : LatchWords) (tree : Exit.sysPath.shape.excessTree = sysExcess p)
    (len : p.len = Exit.sysPath.shape.len)
    (r : Ready sevm b [2, 3, 0, 1]) (hG : gCallStipend < G) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] .empty (G + latchCost Exit.sysPath sevm b))
      (.ok post)) := by
  have hdata : sevm.data.length.toB256 ≠ 0 := data_length_ne hne hlen
  have run := latch_frame_run Exit.sysPath p tree len hfork hstatic hcaller hdata r hG
  exact ⟨_, lift_exact_noExec Exit.sysPath.check Exit.sysPath.jumps hcode
    Exit.sysPath.noExec ⟨_, Exit.sysPath.root, run⟩⟩

/-- **A system-caller frame with empty calldata succeeds at the exit code, under Amsterdam.** -/
theorem progress_system_empty_amsterdam_exit {sevm : Sevm} {b : Devm} {G : Nat}
    (hcode : sevm.code = Exit.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (r : Ready sevm b [2, 3, 0, 1]) (hG : gCallStipend < G) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] .empty (G + RequestSystem.SysPath.frameCost Exit.sysPath sevm b))
      (.ok post)) :=
  ⟨_, RequestSystem.SysPath.frame_exec Exit.sysPath hcode hfork hstatic hcaller hdata r hG⟩

/-! ## System arm, under covered forks

Covered-fork progress holds for non-system callers only (the user arms above carry
`caller ≠ systemAddress` in statement and docstring). There is no SYSTEM-caller theorem at
covered forks. What stands in the way of one: the SYSTEM arm is the Amsterdam drain/latch walk,
and that walk does not generalize within budget. `Ready` (`Blanc/Lift/AmsterdamWalk.lean`) carries
`stateGas.spilled` and `reservoir` fields with no covered counterpart; `rx_sstoreR` requires
`rules.stateGas = some amsterdamStateGasRules` and produces `afterSstoreA` states; the final and
bookkeeping bases and charges (`finalBase`, `bookBase`, `finalGas`, `bookGas`, `setupBase`) are
built on `afterSstoreA`/`sstoreCostA`/`afterSloadA`. A covered walk would re-derive the whole
`RequestSystem` walk layer without state gas, far past a contained change. The protocol issues no
system call before Amsterdam, so the missing combination has no protocol path.
-/

end Blanc.Lift.BuilderRequest
