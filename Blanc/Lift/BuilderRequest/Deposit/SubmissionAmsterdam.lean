import Blanc.Lift.BuilderRequest.Deposit.Frames
import Blanc.Lift.BuilderRequest.UserFrameAmsterdam

/-!
# The deposit runtime's user frames, under Amsterdam

The covered forks' statements in `Deposit.Frames`, at `fork = .amsterdam`. `exec_user_frame_amsterdam` says
every successful non-system frame is a submission or a fee read; `exec_submission_exact_amsterdam` and
`exec_fee_read_amsterdam` construct the execution, with the same record, log and storage.

**Gas.** These hold under any state-gas meter, an empty reservoir included: that is the ordinary case, since
the reservoir holds only gas above the 2^24 execution budget. A store's state gas comes from the reservoir and
then from `gasLeft`, so `submissionGasA` names all a submission takes from `gasLeft`, execution gas and
spill together, and `submissionRepayA` what it gets back from a credit against an earlier spill.

The statements stop at the frame: no message or transaction level, no EIP-7708 transfer log (the frame does
not emit it), no settlement, no history.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune

variable {sevm : Sevm} {b pre post : Devm} {M : Mem} {G : Nat}

/-- The fee path's base after its reads, under Amsterdam: slots 0 and 1 warmed. -/
abbrev feeBaseA (sevm : Sevm) (b : Devm) : Devm := (amsterdamSteps sevm).feeBase b

/-- `STOP` after a submission, under Amsterdam: the whole post state, its state-gas meter included. -/
abbrev submissionPostA (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  Steps.submissionPost (amsterdamSteps sevm) b M G

/-- All a submission takes from `gasLeft` under Amsterdam, from the frame's start: its execution gas and
whatever state gas the reservoir cannot cover. -/
abbrev submissionGasA (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  submissionGasOn (amsterdamSteps sevm) b M iterations

/-- What a submission's stores return to `gasLeft` under Amsterdam: state gas credited against an earlier
spill. Zero unless the frame clears a slot set earlier in its transaction while a spill is outstanding. -/
abbrev submissionRepayA (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  Steps.bodyRepay (amsterdamSteps sevm) (feeBaseA sevm b) M

/-- What a successful submission does under Amsterdam. -/
abbrev SubmittedA (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) : Prop :=
  SubmittedOn (amsterdamSteps sevm) pre post iterations finalOutput

/-- A successful non-system frame at the deposit code under Amsterdam: a submission or a fee read. -/
abbrev UserFrameA (sevm : Sevm) (pre post : Devm) : Prop := UserFrameOn (amsterdamSteps sevm) pre post

/-- **Deposit frames under Amsterdam.** `UserFrames.exec_user_frame_amsterdam` at the deposit code: every successful
execution at a non-system caller, from an empty stack, under any state-gas meter, is a `UserFrameA`. -/
abbrev exec_user_frame_amsterdam := @UserFrames.exec_user_frame_amsterdam frames

/-- **Deposit submission, forward, under Amsterdam, under any state-gas meter.** 184 bytes of calldata in a
non-static frame at a non-system caller, slot 0 off the inhibitor, and the guards' `Admitted` give a successful
execution. It takes `submissionGasA` from `gasLeft`, state gas beyond the reservoir included, and ends with `G`
plus what its credits repay, `slack` being the margin over the `SSTORE` sentry. -/
theorem exec_submission_exact_amsterdam {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 184)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput)
    (admitted : Admitted sevm (finalOutput / (17 : B256))) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGasA sevm b M iterations))
      (.ok (submissionPostA sevm (feeBaseA sevm b) M (G + submissionRepayA sevm b M)))) :=
  exec_submission_on (amsterdamSteps_valid hfork) hcode caller hlen dynamic slack off wordRun admitted

/-- **What the Amsterdam frame does**: the same storage, log and balances as the covered forks'
`Submitted`, under any meter. -/
theorem submissionPostA_effects (hfork : sevm.benvStat.fork = .amsterdam) (hlen : sevm.data.length = 184)
    (wf : Mem.Wf M) (gas : Nat) :
    SubmissionEffects sevm b (submissionPostA sevm (feeBaseA sevm b) M gas) :=
  submissionPost_effects (amsterdamSteps_valid hfork) hlen wf gas

/-- **Deposit fee read, under Amsterdam.** A successful empty-calldata execution at a non-system caller
carries no value, changes no storage, balance or log, and returns the word recurrence's quotient on
`slot0 + max(0, count - 8)`. -/
theorem exec_fee_read_inv_amsterdam (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, UserPath.FeeReadOn (amsterdamSteps sevm) 8 pre post iterations finalOutput :=
  UserPath.exec_fee_read (k := userPath) (amsterdamSteps_valid hfork) hcode stack aligned wf caller empty exec

/-- **Deposit fee read, forward, under Amsterdam.** Empty calldata, no value and slot 0 off the inhibitor at a
non-system caller give a successful execution at the exact charge, returning the word recurrence's quotient
and changing no storage, balance or log. A fee read stores nothing, so the state-gas meter plays no part. The
recurrence always has a finite run (`WordFakeExponential.run_exists`). -/
theorem exec_fee_read_amsterdam {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam)
    (aligned : M.size % 32 = 0) (wf : Mem.Wf M) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGasOn (amsterdamSteps sevm) b M iterations))
        (.ok post)) ∧
      post.output = (finalOutput / (17 : B256)).toBytes ∧
      (∀ a, post.getStor a = b.getStor a) ∧ (∀ a, post.getBal a = b.getBal a) ∧ post.logs = b.logs :=
  UserPath.exec_fee_read_effects (k := userPath) (amsterdamSteps_valid hfork) hcode aligned wf caller empty zero
    off wordRun

/-- **The Amsterdam submission's premises can all be met together, by an ordinary frame.** On storage whose
slots 0 and 1 are zero and have not changed in the transaction, with an empty reservoir (any transaction with a
gas limit below the 2^24 execution budget), all-ones calldata with enough value in a non-static frame runs to
`STOP` with the stated effects. The charge includes the count's `STORAGE_SET`, drawn from `gasLeft`. -/
theorem exec_submission_witness_amsterdam (hcode : sevm.code = code)
    (hfork : sevm.benvStat.fork = .amsterdam) (caller : sevm.caller ≠ systemAddress)
    (data : sevm.data = List.replicate 184 0xff)
    (value : (2 ^ 64 - 1) * 10 ^ 9 + 1 ≤ sevm.value.toNat) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) (slot0 : b.getStorVal sevm.currentTarget 0 = 0)
    (slot1 : b.getStorVal sevm.currentTarget 1 = 0)
    (orig1 : b.getOrigStorVal sevm sevm.currentTarget 1 = 0) (emptyReservoir : b.stateGas.left = 0)
    (wf : Mem.Wf M) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] M (G + submissionGasA sevm b M 1)) (.ok post)) ∧
      SubmissionEffects sevm b post ∧ amsterdamStateGasRules.storageSet ≤ submissionGasA sevm b M 1 := by
  have excess : storedExcess 8 sevm b = 0 := by
    rw [storedExcess, slot0, slot1]
    decide
  have fee : (17 : B256) / (17 : B256) = 1 := by decide
  have hlen : sevm.data.length = 184 := by rw [data]; rfl
  refine ⟨_, exec_submission_exact_amsterdam (finalOutput := 17) hcode hfork caller hlen dynamic slack
    (by rw [slot0]; decide) (by rw [excess]; exact quote_zero_excess)
    (by rw [fee]; exact admitted_witness data value),
    submissionPostA_effects hfork hlen wf _, ?_⟩
  have spill := feeBase_storageSet_le (sevm := sevm) (b := b) slot1 orig1 emptyReservoir
  simp only [submissionGasA, submissionGasOn, Steps.bodyGas]
  omega

end Blanc.Lift.BuilderRequest.Deposit
