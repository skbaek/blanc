import Blanc.Composition.BuilderRequestJointGFate

/-! P4 compatibility corollaries. The explicit prefix condition does not restrict
the run or replace ValidJointG with a minimal-premise interface. -/

namespace Blanc.Lift.BuilderRequest
open Jaune JauneConsensus ExecutionTrace ChainLink Blanc JauneConsensus.Facts.Gloas Occurrence
variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
namespace ValidJointG
variable {checkpoint : BlockChain} {anchor final : GJointState P}


/-- A prefix with no Amsterdam block emits no deposit requests. -/
theorem prefix_deposit_emissions_nil (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    (noAmsterdam : ∀ b ∈ v.preBlocks, b.fork ≠ .amsterdam) :
    Deposit.Indexed.emissions v.preBlocks = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro b member
  exact v.deposit_covered b (List.mem_append_left _ member) (noAmsterdam b member)

/-- A prefix with no Amsterdam block emits no exit requests. -/
theorem prefix_exit_emissions_nil (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    (noAmsterdam : ∀ b ∈ v.preBlocks, b.fork ≠ .amsterdam) :
    Exit.Indexed.emissions v.preBlocks = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro b member
  exact v.exit_covered b (List.mem_append_left _ member) (noAmsterdam b member)

/-- P4 compatibility: preserve the full positional processing/queued fate,
with only the pre-anchor emission case excluded. Ignored outcomes remain processing. -/
theorem deposit_fate_no_pre_anchor_emissions (v : ValidJointG cfg ccfg bls checkpoint anchor final) {n : Nat}
    (noAmsterdam : ∀ b ∈ v.preBlocks, b.fork ≠ .amsterdam)
    (hn : n < (Deposit.Indexed.submissions v.blocks).length) :
    ((Deposit.Indexed.emissions v.preBlocks).length ≤ n ∧ n < (Deposit.Indexed.emissions v.blocks).length ∧
      ∃ bj k, ∃ hbj : bj < v.blocks.length, k < (Deposit.Indexed.blockEmissions v.blocks[bj]).length ∧
        (Deposit.Indexed.emissions (v.blocks.take bj)).length + k = n ∧
        (Deposit.Indexed.blockEmissions v.blocks[bj])[k]? = (Deposit.Indexed.submissions v.blocks)[n]? ∧
        v.preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderDepositRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        v.run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ v.run.payloadIndex j = bj - v.preBlocks.length ∧
        D.builderDeposits[k]? = some req ∧ Ssz.serialize req = (Deposit.Indexed.submissions v.blocks)[n]! ∧
        builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderDeposit ccfg bls m req = .ok o ∧
          (∀ o', classifyBuilderDeposit ccfg bls m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderDepositOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req', v.run.steps[j']? = some (.gloas D') →
            D'.builderDeposits[k']? = some req' →
            (Deposit.Indexed.emissions (v.blocks.take (v.preBlocks.length + v.run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Deposit.Indexed.emissions v.blocks).length ≤ n ∧
      (Deposit.Indexed.remainingQueue final.exec)[n - (Deposit.Indexed.emissions v.blocks).length]? =
        (Deposit.Indexed.submissions v.blocks)[n]?) := by
  rcases v.deposit_fate hn with ⟨before, _⟩ | later
  · rw [v.prefix_deposit_emissions_nil noAmsterdam, List.length_nil] at before
    exact (Nat.not_lt_zero _ before).elim
  · exact later

/-- P4 compatibility: preserve the full positional processing/queued fate,
with only the pre-anchor emission case excluded. Ignored outcomes remain processing. -/
theorem exit_fate_no_pre_anchor_emissions (v : ValidJointG cfg ccfg bls checkpoint anchor final) {n : Nat}
    (noAmsterdam : ∀ b ∈ v.preBlocks, b.fork ≠ .amsterdam)
    (hn : n < (Exit.Indexed.submissions v.blocks).length) :
    ((Exit.Indexed.emissions v.preBlocks).length ≤ n ∧ n < (Exit.Indexed.emissions v.blocks).length ∧
      ∃ bj k, ∃ hbj : bj < v.blocks.length, k < (Exit.Indexed.blockEmissions v.blocks[bj]).length ∧
        (Exit.Indexed.emissions (v.blocks.take bj)).length + k = n ∧
        (Exit.Indexed.blockEmissions v.blocks[bj])[k]? = (Exit.Indexed.submissions v.blocks)[n]? ∧
        v.preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderExitRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        v.run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ v.run.payloadIndex j = bj - v.preBlocks.length ∧
        D.builderExits[k]? = some req ∧ Ssz.serialize req = (Exit.Indexed.submissions v.blocks)[n]! ∧
        builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderExit ccfg m req = .ok o ∧
          (∀ o', classifyBuilderExit ccfg m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderExitOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req', v.run.steps[j']? = some (.gloas D') →
            D'.builderExits[k']? = some req' →
            (Exit.Indexed.emissions (v.blocks.take (v.preBlocks.length + v.run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Exit.Indexed.emissions v.blocks).length ≤ n ∧
      (Exit.Indexed.remainingQueue final.exec)[n - (Exit.Indexed.emissions v.blocks).length]? =
        (Exit.Indexed.submissions v.blocks)[n]?) := by
  rcases v.exit_fate hn with ⟨before, _⟩ | later
  · rw [v.prefix_exit_emissions_nil noAmsterdam, List.length_nil] at before
    exact (Nat.not_lt_zero _ before).elim
  · exact later

end ValidJointG
end Blanc.Lift.BuilderRequest

