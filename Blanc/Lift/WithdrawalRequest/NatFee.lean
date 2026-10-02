import Blanc.Lift.WithdrawalRequest.FrameEffects
import Blanc.Lift.WithdrawalRequest.UserGas
import Blanc.FakeExponentialWordCorrespondence

/-! Explicit sufficient no-wrap fee correspondence consumed by actual frame
results and fresh liveness. No reachable or maximal-domain claim is made. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- A finite existing Nat trace with the accepted prefixed no-wrap bounds. -/
def NatFeeDomain (excess : B256) (iterations : Nat) : Prop :=
  ∃ output, ∃ run : FakeExponential.Run excess.toNat
      Blanc.WithdrawalRequest.feeUpdateFraction 1 Blanc.WithdrawalRequest.feeUpdateFraction
      iterations output, FakeExponentialWordCorrespondence.NoWrap run 0

/-- Every executed word trace has this Nat trace's count and the unchanged
model fee; only the excess identity is needed from a model state. -/
theorem NatFeeDomain.word_result {excess : B256} {iterations wordIterations : Nat}
    {wordOutput : B256} (domain : NatFeeDomain excess iterations)
    (model : Blanc.WithdrawalRequest.State) (excessEq : model.excess = excess.toNat)
    (wordRun : WordFakeExponential.Run excess 17 1 17 0 wordIterations wordOutput) :
    wordIterations = iterations ∧
      (wordOutput / (17 : B256)).toNat = Blanc.WithdrawalRequest.fee model ∧
      wordOutput / (17 : B256) = (Blanc.WithdrawalRequest.fee model).toB256 := by
  obtain ⟨output, run, safe⟩ := domain
  have imageRun : WordFakeExponential.Run excess.toNat.toB256 (17 : Nat).toB256 1
      ((1 : Nat).toB256 * (17 : Nat).toB256) 0 wordIterations wordOutput := by
    rw [toB256_toNat]
    exact wordRun
  have same := safe.fakeExp_eq (factor := 1) (by decide) imageRun
  have feeEq : (wordOutput / (17 : B256)).toNat = Blanc.WithdrawalRequest.fee model := by
    rw [Blanc.WithdrawalRequest.fee, excessEq]
    exact same.2
  refine ⟨same.1, feeEq, ?_⟩
  rw [← feeEq, toB256_toNat]

/-- Actual successful submission admission uses the canonical Nat fee on the
named sufficient domain. No queue representation is required. -/
theorem FrameEffect.submission_paid_nat {sevm : Sevm} {pre post : Devm} {iterations : Nat}
    (effect : FrameEffect sevm pre post) (user : sevm.caller ≠ systemAddress)
    (length : sevm.data.length = 56)
    (domain : NatFeeDomain (pre.getStorVal sevm.currentTarget 0) iterations)
    (model : Blanc.WithdrawalRequest.State)
    (excessEq : model.excess = (pre.getStorVal sevm.currentTarget 0).toNat) :
    Blanc.WithdrawalRequest.fee model ≤ sevm.value.toNat := by
  cases effect with
  | system caller _ _ _ => exact (user caller).elim
  | submission _ _ _ _ wordIterations wordOutput wordRun paid _ _ =>
    rw [(domain.word_result model excessEq wordRun).2.1] at paid
    exact paid
  | getter _ empty _ _ _ _ _ _ _ _ =>
    simp only [empty, List.length_nil] at length
    omega

/-- The actual getter's RETURN bytes encode the canonical Nat fee on the same
sufficient domain; the model contributes only its excess value. -/
theorem FrameEffect.getter_output_nat {sevm : Sevm} {pre post : Devm} {iterations : Nat}
    (effect : FrameEffect sevm pre post) (user : sevm.caller ≠ systemAddress)
    (empty : sevm.data = [])
    (domain : NatFeeDomain (pre.getStorVal sevm.currentTarget 0) iterations)
    (model : Blanc.WithdrawalRequest.State)
    (excessEq : model.excess = (pre.getStorVal sevm.currentTarget 0).toNat) :
    post.output = (Blanc.WithdrawalRequest.fee model).toB256.toBytes := by
  cases effect with
  | system caller _ _ _ => exact (user caller).elim
  | submission _ _ length _ _ _ _ _ _ _ =>
    simp only [empty, List.length_nil] at length
    omega
  | getter _ _ _ _ wordIterations wordOutput wordRun _ _ output =>
    rw [output, (domain.word_result model excessEq wordRun).2.2]

/-- Consume the correspondence on an actual successful canonical raw frame. -/
theorem exec_user_nat_fee {sevm : Sevm} {pre post : Devm} {iterations : Nat}
    (code : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (user : sevm.caller ≠ systemAddress)
    (domain : NatFeeDomain (pre.getStorVal sevm.currentTarget 0) iterations)
    (model : Blanc.WithdrawalRequest.State)
    (excessEq : model.excess = (pre.getStorVal sevm.currentTarget 0).toNat)
    (run : Exec 0 sevm pre (.ok post)) :
    (sevm.data.length = 56 → Blanc.WithdrawalRequest.fee model ≤ sevm.value.toNat) ∧
    (sevm.data = [] → post.output = (Blanc.WithdrawalRequest.fee model).toB256.toBytes) := by
  have effect := exec_frame_effect code fork stack aligned wf lengthBound run
  exact ⟨fun length => effect.submission_paid_nat user length domain model excessEq,
    fun empty => effect.getter_output_nat user empty domain model excessEq⟩


end Blanc.Lift.WithdrawalRequest
