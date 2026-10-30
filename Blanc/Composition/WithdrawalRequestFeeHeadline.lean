import Blanc.Composition.WithdrawalRequestFeeRefutation
import Blanc.Lift.WithdrawalRequest.HeadlineFee

/-!
# The refutation of the mathematical-fee guarantee, without the model

The statement reads only the checkpoint's code and storage words, the committed submission
frames of the history, their stored excess and paid value, and the bytecode's word fee loop.
It is equivalent to `NatFeeGuaranteeRefuted`, whose witness it reuses.
-/

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample

open Jaune Blanc.Lift Blanc.ExecutionTrace

/-- Some configured history, from a checkpoint with the system contracts installed, empty
SYSTEM code and EIP-7002 storage as deployed, under the SYSTEM-sender, 7702-authority and
CREATE-avoidance exclusions, has a committed submission that paid the bytecode's fee at its
stored excess but less than `fake_exponential(1, excess, 17)`. -/
def FeeGuaranteeRefuted : Prop :=
  ∃ (cfg : ChainConfig) (checkpoint future : BlockChain)
    (trace : ConfiguredHistoryTrace cfg checkpoint future),
    SystemCodeInstalled checkpoint.state ∧
    trace.NoSenderAt systemAddress ∧ trace.NoAuthorityAt systemAddress ∧
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress = ByteArray.empty ∧
    InitialStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get ∧
    ∃ frame ∈ submissionFrames trace,
      (∃ iterations output,
        WordFakeExponential.Run (storedExcess frame.pre.state) 17 1 17 0 iterations output ∧
        WordFee output ≤ paid frame) ∧
      paid frame < SpecFee (storedExcess frame.pre.state)

/-- The model-free statement is the model statement with `fee model` read as
`fake_exponential(1, excess, 17)` and initial storage read as its four words. -/
theorem feeGuaranteeRefuted_iff : FeeGuaranteeRefuted ↔ NatFeeGuaranteeRefuted := by
  constructor
  · rintro ⟨cfg, checkpoint, future, trace, installed, senders, authorities, avoid, systemEmpty,
      init, frame, member, ⟨iterations, output, run, paidFee⟩, below⟩
    obtain ⟨member, submission⟩ := (mem_submissionFrames trace frame).1 member
    refine ⟨cfg, checkpoint, future, trace, installed, senders, authorities, avoid, systemEmpty,
      (representsStorage_initial_iff _).2 init, frame, member, ⟨(storedExcess frame.pre.state).toNat,
        0, 0, 0, []⟩, iterations, output, submission, rfl, run, paidFee, ?_⟩
    rw [← specFee_eq_fee _ (storedExcess frame.pre.state) rfl]
    exact below
  · rintro ⟨cfg, checkpoint, future, trace, installed, senders, authorities, avoid, systemEmpty,
      init, frame, member, model, iterations, output, submission, excessEq, run, paidFee, below⟩
    refine ⟨cfg, checkpoint, future, trace, installed, senders, authorities, avoid, systemEmpty,
      (representsStorage_initial_iff _).1 init, frame,
      (mem_submissionFrames trace frame).2 ⟨member, submission⟩,
      ⟨iterations, output, run, paidFee⟩, ?_⟩
    rw [specFee_eq_fee model (storedExcess frame.pre.state) excessEq]
    exact below

/-- **The EIP-7002 fee guarantee is refuted.** A committed submission in a configured history
from an initialized checkpoint paid the bytecode's fee yet less than the EIP's
`fake_exponential(1, excess, 17)`. -/
theorem fee_guarantee_refuted : FeeGuaranteeRefuted :=
  feeGuaranteeRefuted_iff.2 nat_fee_guarantee_refuted

end Blanc.Lift.WithdrawalRequest.FeeCounterexample
