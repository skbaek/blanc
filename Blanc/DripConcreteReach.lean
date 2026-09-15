-- DripConcreteReach.lean : configured reach for the literal DRIP history.

import Blanc.DripConcreteHistory
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryExact
import Blanc.BalanceAlgebra

namespace Blanc
namespace Drip

open Jaune

/-- Only the signed sender is funded in the literal private genesis. The
four protocol-code accounts carry zero balance. -/
theorem concreteGenesisBalance_other (a : Adr) (sender : a ≠ concreteCreateSender) :
    concreteGenesisState.bal a = 0 := by
  change (concreteGenesisState.get a).bal = 0
  unfold concreteGenesisState State.ofList
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases consolidation : consolidationRequestPredeployAddress = a
  · rw [consolidation, State.get_set_self]
    rfl
  rw [State.get_set_ne _ consolidation]
  by_cases withdrawal : withdrawalRequestPredeployAddress = a
  · rw [withdrawal, State.get_set_self]
    rfl
  rw [State.get_set_ne _ withdrawal]
  by_cases history : historyStorageAddress = a
  · rw [history, State.get_set_self]
    rfl
  rw [State.get_set_ne _ history]
  by_cases beacon : beaconRootsAddress = a
  · rw [beacon, State.get_set_self]
    rfl
  rw [State.get_set_ne _ beacon, State.get_set_ne _ sender.symm]
  rfl

/-- Sparse-map summation proves the genesis funding without enumerating the
address space. -/
theorem concreteGenesis_sum :
    sum concreteGenesisState.bal = 1000000000000000000 := by
  have row : (concreteGenesisState.bal concreteCreateSender).toNat =
      (0 : B256).toNat + 1000000000000000000 := by
    change (concreteGenesisState.get concreteCreateSender).bal.toNat = _
    rw [concreteGenesisSender]
    decide +kernel
  have total := sum_eq_add_of_row_add (f := fun _ => (0 : B256))
    row concreteGenesisBalance_other
  have zero : sum (fun _ => (0 : B256)) = 0 := sumBelow_zero _
  exact total.trans ((congrArg (fun n => n + 1000000000000000000) zero).trans
    (Nat.zero_add _))

theorem concreteDeployed_sum_le :
    sum concreteDeployed.state.bal ≤ sum concreteBase.state.bal :=
  concreteDeploymentTrace.sum_le_of_empty_withdrawals

theorem concreteJoined_sum_le :
    sum concreteJoined.state.bal ≤ sum concreteDeployed.state.bal := by
  rcases ExecutionTrace.exists_appliedBodyTrace concreteJoin_body with ⟨trace⟩
  exact trace.sum_le_of_empty_withdrawals

theorem concreteDripped_sum_le :
    sum concreteDripped.state.bal ≤ sum concreteJoined.state.bal := by
  rcases ExecutionTrace.exists_appliedBodyTrace concreteDrip_body with ⟨trace⟩
  exact trace.sum_le_of_empty_withdrawals

theorem concreteExited_sum_le :
    sum concreteExited.state.bal ≤ sum concreteDripped.state.bal := by
  rcases ExecutionTrace.exists_appliedBodyTrace concreteExit_body with ⟨trace⟩
  exact trace.sum_le_of_empty_withdrawals

/-- Each strict bound belongs to its actual world; the preceding world's
bound is the one consumed by the next configured reach step. -/
theorem concrete_world_sum_bounds :
    sum concreteBase.state.bal < 2 ^ 256 ∧
      sum concreteDeployed.state.bal < 2 ^ 256 ∧
      sum concreteJoined.state.bal < 2 ^ 256 ∧
      sum concreteDripped.state.bal < 2 ^ 256 ∧
      sum concreteExited.state.bal < 2 ^ 256 := by
  have base : sum concreteBase.state.bal < 2 ^ 256 := by
    change sum concreteGenesisState.bal < 2 ^ 256
    rw [concreteGenesis_sum]
    decide +kernel
  have deployed := lt_of_le_of_lt concreteDeployed_sum_le base
  have joined := lt_of_le_of_lt concreteJoined_sum_le deployed
  have dripped := lt_of_le_of_lt concreteDripped_sum_le joined
  have exited := lt_of_le_of_lt concreteExited_sum_le dripped
  exact ⟨base, deployed, joined, dripped, exited⟩

/-- The literal private genesis is a valid starting point for the selected
chain configuration. -/
theorem concreteBase_reach :
    BlockChain.ReachUsing concreteConfig concreteBase concreteBase :=
  .refl concreteBase (ChainConfig.pragueOnly_valid 1) concreteBase_validContext rfl

theorem concreteDeployed_reach :
    BlockChain.ReachUsing concreteConfig concreteBase concreteDeployed := by
  refine .step concreteBase_reach ?_ concreteDeploymentStep
  have empty : wdsum concreteDeploymentEnvelope.block.wds = 0 := rfl
  have balance : sum concreteBase.state.bal + wdsum concreteDeploymentEnvelope.block.wds =
      sum concreteBase.state.bal :=
    (congrArg (fun n => sum concreteBase.state.bal + n) empty).trans (Nat.add_zero _)
  exact (congrArg (fun n => n < 2 ^ 256) balance).mpr concrete_world_sum_bounds.1

theorem concreteJoined_reach :
    BlockChain.ReachUsing concreteConfig concreteBase concreteJoined := by
  refine .step concreteDeployed_reach ?_ concreteJoin_step
  have empty : wdsum concreteJoinBlock.wds = 0 := rfl
  have balance : sum concreteDeployed.state.bal + wdsum concreteJoinBlock.wds =
      sum concreteDeployed.state.bal :=
    (congrArg (fun n => sum concreteDeployed.state.bal + n) empty).trans (Nat.add_zero _)
  exact (congrArg (fun n => n < 2 ^ 256) balance).mpr concrete_world_sum_bounds.2.1

theorem concreteDripped_reach :
    BlockChain.ReachUsing concreteConfig concreteBase concreteDripped := by
  refine .step concreteJoined_reach ?_ concreteDrip_step
  have empty : wdsum concreteDripBlock.wds = 0 := rfl
  have balance : sum concreteJoined.state.bal + wdsum concreteDripBlock.wds =
      sum concreteJoined.state.bal :=
    (congrArg (fun n => sum concreteJoined.state.bal + n) empty).trans (Nat.add_zero _)
  exact (congrArg (fun n => n < 2 ^ 256) balance).mpr concrete_world_sum_bounds.2.2.1

/-- All four actual configured transitions, including deployment, form one
reach from the literal genesis to the paid exit world. -/
theorem concreteExited_reach :
    BlockChain.ReachUsing concreteConfig concreteBase concreteExited := by
  refine .step concreteDripped_reach ?_ concreteExit_step
  have empty : wdsum concreteExitBlock.wds = 0 := rfl
  have balance : sum concreteDripped.state.bal + wdsum concreteExitBlock.wds =
      sum concreteDripped.state.bal :=
    (congrArg (fun n => sum concreteDripped.state.bal + n) empty).trans (Nat.add_zero _)
  exact (congrArg (fun n => n < 2 ^ 256) balance).mpr concrete_world_sum_bounds.2.2.2.1

/-- Typed retained traces for the four actual transitions. Each producer
uses the bound on its input world, before the block executes. -/
noncomputable def concreteDeploymentBlockTrace :
    ExecutionTrace.ConfiguredBlockTrace concreteConfig concreteBase concreteDeployed :=
  Classical.choice (ExecutionTrace.exists_configuredBlockTrace_of_transition
    (block := concreteDeploymentEnvelope.block) (by
      have empty : wdsum concreteDeploymentEnvelope.block.wds = 0 := rfl
      have balance : sum concreteBase.state.bal + wdsum concreteDeploymentEnvelope.block.wds =
          sum concreteBase.state.bal :=
        (congrArg (fun n => sum concreteBase.state.bal + n) empty).trans (Nat.add_zero _)
      exact (congrArg (fun n => n < 2 ^ 256) balance).mpr
        concrete_world_sum_bounds.1)
    concreteDeploymentStep)

noncomputable def concreteJoinBlockTrace :
    ExecutionTrace.ConfiguredBlockTrace concreteConfig concreteDeployed concreteJoined :=
  Classical.choice (ExecutionTrace.exists_configuredBlockTrace_of_transition
    (block := concreteJoinBlock) (by
      have empty : wdsum concreteJoinBlock.wds = 0 := rfl
      have balance : sum concreteDeployed.state.bal + wdsum concreteJoinBlock.wds =
          sum concreteDeployed.state.bal :=
        (congrArg (fun n => sum concreteDeployed.state.bal + n) empty).trans (Nat.add_zero _)
      exact (congrArg (fun n => n < 2 ^ 256) balance).mpr
        concrete_world_sum_bounds.2.1)
    concreteJoin_step)

noncomputable def concreteDripBlockTrace :
    ExecutionTrace.ConfiguredBlockTrace concreteConfig concreteJoined concreteDripped :=
  Classical.choice (ExecutionTrace.exists_configuredBlockTrace_of_transition
    (block := concreteDripBlock) (by
      have empty : wdsum concreteDripBlock.wds = 0 := rfl
      have balance : sum concreteJoined.state.bal + wdsum concreteDripBlock.wds =
          sum concreteJoined.state.bal :=
        (congrArg (fun n => sum concreteJoined.state.bal + n) empty).trans (Nat.add_zero _)
      exact (congrArg (fun n => n < 2 ^ 256) balance).mpr
        concrete_world_sum_bounds.2.2.1)
    concreteDrip_step)

noncomputable def concreteExitBlockTrace :
    ExecutionTrace.ConfiguredBlockTrace concreteConfig concreteDripped concreteExited :=
  Classical.choice (ExecutionTrace.exists_configuredBlockTrace_of_transition
    (block := concreteExitBlock) (by
      have empty : wdsum concreteExitBlock.wds = 0 := rfl
      have balance : sum concreteDripped.state.bal + wdsum concreteExitBlock.wds =
          sum concreteDripped.state.bal :=
        (congrArg (fun n => sum concreteDripped.state.bal + n) empty).trans (Nat.add_zero _)
      exact (congrArg (fun n => n < 2 ^ 256) balance).mpr
        concrete_world_sum_bounds.2.2.2.1)
    concreteExit_step)

/-- The named typed traces retain these literal blocks, not just the same
endpoints. No transition's body evidence is reconstructed here. -/
theorem concreteBlockTraces_blocks :
    concreteDeploymentBlockTrace.block = concreteDeploymentEnvelope.block ∧
    concreteJoinBlockTrace.block = concreteJoinBlock ∧
    concreteDripBlockTrace.block = concreteDripBlock ∧
    concreteExitBlockTrace.block = concreteExitBlock :=
  ⟨concreteDeploymentBlockTrace.block_eq_of_transition concreteDeploymentStep,
    concreteJoinBlockTrace.block_eq_of_transition concreteJoin_step,
    concreteDripBlockTrace.block_eq_of_transition concreteDrip_step,
    concreteExitBlockTrace.block_eq_of_transition concreteExit_step⟩

/-- Retain the four named block/body executions as an explicit constructor
spine, with every intermediate world fixed by the block trace's type. -/
noncomputable def concreteConfiguredHistory :
    ExecutionTrace.ConfiguredHistoryTrace concreteConfig concreteBase concreteExited :=
  .step (.step (.step (.step
    (.refl (ChainConfig.pragueOnly_valid 1) concreteBase_validContext rfl)
    concreteDeploymentBlockTrace) concreteJoinBlockTrace)
    concreteDripBlockTrace) concreteExitBlockTrace

/-- Expose the literal constructor spine and its four block identities. -/
theorem concreteConfiguredHistory_exact :
    concreteConfiguredHistory =
      .step (.step (.step (.step
        (.refl (ChainConfig.pragueOnly_valid 1) concreteBase_validContext rfl)
        concreteDeploymentBlockTrace) concreteJoinBlockTrace)
        concreteDripBlockTrace) concreteExitBlockTrace ∧
    (concreteDeploymentBlockTrace.block = concreteDeploymentEnvelope.block ∧
      concreteJoinBlockTrace.block = concreteJoinBlock ∧
      concreteDripBlockTrace.block = concreteDripBlock ∧
      concreteExitBlockTrace.block = concreteExitBlock) :=
  ⟨rfl, concreteBlockTraces_blocks⟩

/-- The linked configured history ends at the proved exit storage, balances,
receipt and return/gas observations. Family accounting realization is separate. -/
theorem concreteHistory_checkpoint :
    BlockChain.ReachUsing concreteConfig concreteBase concreteExited ∧
    Nonempty (ExecutionTrace.ConfiguredHistoryTrace concreteConfig concreteBase concreteExited) ∧
    ((concreteExited.state.getStor concreteCreateTarget).get chiSlot = concreteExitChi ∧
      (concreteExited.state.getStor concreteCreateTarget).get rhoSlot = 6 ∧
      (concreteExited.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 59 ∧
      (concreteExited.state.getStor concreteCreateTarget).get totalUnitsSlot = 59) ∧
    concreteExited.state.bal concreteCreateTarget = 60 ∧
    concreteExited.state.bal concreteCreateSender = 999999999998725850 ∧
    concreteExited.state.getNonce concreteCreateSender = 4 ∧
    (concreteExitTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true ∧
    (concreteExitMessageOutput.returnData = (40 : B256).toBytes ∧
      concreteExitTransactionBout.blockGasUsed = 48917 ∧
      concreteExitTransactionBout.blockLogs = [] ∧
      concreteExitBlock.header.timestamp = 6 ∧ concreteExitBlock.header.number = 4) :=
  ⟨concreteExited_reach, ⟨concreteConfiguredHistory⟩, concreteExited_values,
    concreteExitedTargetBalance, concreteExitedSenderBalance, concreteExitedSenderNonce,
    concreteExit_receiptSucceeded, concreteExit_observations⟩

end Drip
end Blanc
