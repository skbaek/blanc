import Blanc.Lift.WithdrawalRequest.ExactFeeDomain
import Blanc.Lift.WithdrawalRequest.BalanceHistory

/-!
# The EIP-7002 fee, stated against `fake_exponential` directly

The observers below read only a storage word, a call frame's value, or the word
loop's output. The headlines compare the bytecode's fee with the EIP's
`fake_exponential(1, excess, 17)` (Jaune's `fakeExp`), with no model state.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace

/-- The EIP's fee at stored excess `excess`: `fake_exponential(1, excess, 17)`. -/
def SpecFee (excess : B256) : Nat := fakeExp 1 excess.toNat 17

/-- The fee the bytecode charges from its word fee loop's output. -/
def WordFee (output : B256) : Nat := (output / (17 : B256)).toNat

/-- The excess word (slot 0) stored in the EIP-7002 account of a world state. -/
def storedExcess (world : Jaune.State) : B256 :=
  (world.getStor withdrawalRequestPredeployAddress).get 0

/-- The value a call frame paid, in wei. -/
def paid (frame : Exec.Frame) : Nat := frame.sevm.value.toNat

/-- The committed EIP-7002 submission frames of a history, in execution order: settled,
nonstatic, non-SYSTEM calls to EIP-7002 with exactly 56 bytes of calldata. -/
def submissionFrames {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) : List Exec.Frame :=
  (history.settledFrames.flatMap submissionFramePayments).map Prod.fst

/-- EIP-7002 storage as deployed: inhibitor excess, and zero count, head and tail. -/
def InitialStorage (storage : B256 → B256) : Prop :=
  storage 0 = B256.max ∧ storage 1 = 0 ∧ storage 2 = 0 ∧ storage 3 = 0

/-- **EIP-7002 fee bound.** The fee the bytecode computes from excess `excess` is at most
the EIP's `fake_exponential(1, excess, 17)`. -/
theorem fee_le_spec {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output ≤ SpecFee excess :=
  word_fee_le_nat run ⟨excess.toNat, 0, 0, 0, []⟩ rfl

/-- **EIP-7002 exact fee.** The bytecode's fee equals `fake_exponential(1, excess, 17)`
exactly on the no-wrap domain `NatFeeDomain` of the executed loop. -/
theorem fee_eq_spec_iff {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output = SpecFee excess ↔ NatFeeDomain excess iterations :=
  word_fee_eq_iff_natFeeDomain run ⟨excess.toNat, 0, 0, 0, []⟩ rfl

/-! Correspondence of the observers to the internal model. -/

theorem specFee_eq_fee (model : Blanc.WithdrawalRequest.State) (excess : B256)
    (excessEq : model.excess = excess.toNat) : SpecFee excess = Blanc.WithdrawalRequest.fee model := by
  rw [SpecFee, Blanc.WithdrawalRequest.fee, excessEq]
  rfl

theorem mem_submissionFrames {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) (frame : Exec.Frame) :
    frame ∈ submissionFrames history ↔
      frame ∈ history.settledFrames.flatMap balanceFrameObservation ∧
        submissionPaymentFrame frame := by
  simp only [submissionFrames, List.mem_map, List.mem_flatMap, submissionFramePayments,
    balanceFrameObservation]
  constructor
  · rintro ⟨pair, ⟨root, member, inner⟩, rfl⟩
    by_cases submission : submissionPaymentFrame root
    · rw [ite_eq_left submission, List.mem_singleton] at inner
      subst inner
      exact ⟨⟨root, member, by rw [ite_eq_left submission.1]; exact List.mem_singleton_self _⟩,
        submission⟩
    · rw [ite_eq_right submission] at inner
      exact absurd inner List.not_mem_nil
  · rintro ⟨⟨root, member, inner⟩, submission⟩
    by_cases observed : root.sevm.currentTarget = withdrawalRequestPredeployAddress ∧
        root.sevm.isStatic = false
    · rw [ite_eq_left observed, List.mem_singleton] at inner
      subst inner
      exact ⟨(frame, frame.sevm.value.toNat),
        ⟨frame, member, by rw [ite_eq_left submission]; exact List.mem_singleton_self _⟩, rfl⟩
    · rw [ite_eq_right observed] at inner
      exact absurd inner List.not_mem_nil

theorem representsStorage_initial_iff (storage : B256 → B256) :
    Blanc.WithdrawalRequest.RepresentsStorage storage Blanc.WithdrawalRequest.initial ↔
      InitialStorage storage := by
  constructor
  · intro rep
    exact ⟨rep.excess, rep.count, rep.head, rep.tail⟩
  · rintro ⟨excess, count, head, tail⟩
    refine ⟨Blanc.WithdrawalRequest.initial_coherent,
      ⟨by decide, by decide, by decide, by decide, ?_⟩, excess, count, head, tail, ?_⟩
    · intro i hi
      exact False.elim (Nat.not_lt_zero i hi)
    · intro i hi
      exact False.elim (Nat.not_lt_zero i hi)

end Blanc.Lift.WithdrawalRequest
