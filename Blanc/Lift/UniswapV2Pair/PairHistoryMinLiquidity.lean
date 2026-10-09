import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.PropertiesMinLiquidity

/-!
# The Pair's `MINIMUM_LIQUIDITY` floor over a configured history

From the deployment checkpoint (`pair_history_initialized`), with the Pair not at address zero and no
zero caller among the history's own steps (re-entered children included), the supply is zero or
address zero holds at least `MINIMUM_LIQUIDITY` LP at every outermost replay boundary, and once
positive the supply never falls below 1000 (`pair_history_minimum_liquidity`). With the fee-off
share-value law this makes the outgoing supply of every positive-supply boundary positive, so the
ratio form `r0·r1/T² ≤ r0'·r1'/T'²` is well defined (`pair_history_feeOff_ratio`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

private theorem initialized_supplyFloor (factory : Adr) (domain : B256) (token0 token1 : Adr) :
    (initializedState factory domain token0 token1).SupplyFloor :=
  ⟨Or.inl B256.toNat_zero, fun _ => rfl⟩

private theorem steps_pair_nonzero_with
    {Auth : Exec.Deriv → Entry → Transcript → Prop} {pair : Adr} {steps : List PairStep}
    (auth : ∀ s ∈ steps, s.AuthenticWith Auth pair) (nonzero : pair ≠ 0) :
    ∀ inv ∈ steps.map PairStep.source, inv.context.pair ≠ 0 := by
  intro inv member
  obtain ⟨s, sMem, rfl⟩ := List.mem_map.mp member
  change s.frame.sevm.currentTarget ≠ 0
  rw [(auth s sMem).2.2.1]
  exact nonzero

theorem pair_history_minimum_liquidity_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (ledger : st₀.Ledger)
    (floor : st₀.SupplyFloor)
    (nonzero : pair ≠ 0) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith Auth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith Consumes st₀ steps finish ∧
        runSourceInvocations st₀
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        ((∀ s ∈ steps, s.source.CallersNonzero) →
          finish.SupplyFloor ∧
          ∀ before after, (before, after) ∈ sourceReplayEdges
              st₀ (steps.map PairStep.source) →
            before.SupplyFloor ∧ after.SupplyFloor ∧
              (0 < before.totalSupply.toNat → 1000 ≤ after.totalSupply.toNat)) := by
  obtain ⟨_, steps, observed, auth, finish, K', matched, source, realized, _, _, rep⟩ :=
    pair_history_committed_with supplies weaken trace installed initial fresh
  refine ⟨steps, observed, auth, finish, K', matched, realized, rep, fun callers => ?_⟩
  exact source.supplyFloor floor ledger
    (steps_pair_nonzero_with auth nonzero)
    (fun inv member => by
      obtain ⟨s, sMem, rfl⟩ := List.mem_map.mp member
      exact callers s sMem)

theorem pair_history_feeOff_ratio_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (ledger : st₀.Ledger)
    (floor : st₀.SupplyFloor)
    (nonzero : pair ≠ 0) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith Auth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith Consumes st₀ steps finish ∧
        runSourceInvocations st₀
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswers st₀
            (steps.map PairStep.source) →
          (∀ s ∈ steps, s.source.CallersNonzero) →
          ∀ before after, (before, after) ∈ sourceReplayEdges
              st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            1000 ≤ after.totalSupply.toNat ∧
              ((before.reserve0.val * before.reserve1.val : ℚ) / (before.totalSupply.toNat : ℚ) ^ 2 ≤
                (after.reserve0.val * after.reserve1.val : ℚ) / (after.totalSupply.toNat : ℚ) ^ 2)) := by
  obtain ⟨_, steps, observed, auth, finish, K', matched, source, realized, _, _, rep⟩ :=
    pair_history_committed_with supplies weaken trace installed initial fresh
  refine ⟨steps, observed, auth, finish, K', matched, realized, rep, fun answers callers => ?_⟩
  have floors := (source.supplyFloor floor ledger
    (steps_pair_nonzero_with auth nonzero)
    (fun inv member => by
      obtain ⟨s, sMem, rfl⟩ := List.mem_map.mp member
      exact callers s sMem)).2
  intro before after member positive
  have outgoing := (floors before after member).2.2 positive
  refine ⟨outgoing, ?_⟩
  have product := source.feeOff_product answers before after member positive
  have beforePos : (0 : ℚ) < (before.totalSupply.toNat : ℚ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr positive) 2
  have afterPos : (0 : ℚ) < (after.totalSupply.toNat : ℚ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) outgoing)) 2
  rw [div_le_div_iff₀ beforePos afterPos]
  exact_mod_cast product

/-- Minimum-liquidity preservation from any represented checkpoint satisfying `State.Ledger` and `State.SupplyFloor`. -/
theorem pair_history_minimum_liquidity_from_checkpoint
    {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (ledger : st₀.Ledger)
    (floor : st₀.SupplyFloor)
    (nonzero : pair ≠ 0) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        ((∀ s ∈ steps, s.source.CallersNonzero) →
          finish.SupplyFloor ∧
          ∀ before after, (before, after) ∈ sourceReplayEdges
              st₀ (steps.map PairStep.source) →
            before.SupplyFloor ∧ after.SupplyFloor ∧
              (0 < before.totalSupply.toNat → 1000 ≤ after.totalSupply.toNat)) :=
  pair_history_minimum_liquidity_with
    (fun _ inj apart => pairAdmittedSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed.positional.forget) trace installed initial fresh ledger floor nonzero

/-- Fee-off share-value ratio preservation from any represented checkpoint satisfying `State.Ledger` and `State.SupplyFloor`. -/
theorem pair_history_feeOff_ratio_from_checkpoint
    {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (ledger : st₀.Ledger)
    (floor : st₀.SupplyFloor)
    (nonzero : pair ≠ 0) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswers st₀
            (steps.map PairStep.source) →
          (∀ s ∈ steps, s.source.CallersNonzero) →
          ∀ before after, (before, after) ∈ sourceReplayEdges
              st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            1000 ≤ after.totalSupply.toNat ∧
              ((before.reserve0.val * before.reserve1.val : ℚ) / (before.totalSupply.toNat : ℚ) ^ 2 ≤
                (after.reserve0.val * after.reserve1.val : ℚ) / (after.totalSupply.toNat : ℚ) ^ 2)) :=
  pair_history_feeOff_ratio_with
    (fun _ inj apart => pairAdmittedSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed.positional.forget) trace installed initial fresh ledger floor nonzero

/-- **`MINIMUM_LIQUIDITY` keeps the supply positive (U3 floor).**  For a configured history from the
deployment checkpoint of a Pair not at address zero: if no step of the history, and no re-entered
Pair child consumed inside a step's transcript, has caller zero (`SourceInvocation.CallersNonzero`,
over exactly these steps), then the final model state and both ends of every outermost replay
boundary satisfy `State.SupplyFloor` — the supply is zero or address zero holds at least 1000 LP, and
address zero has granted no allowance — and every step entered with positive supply leaves at least
1000. -/
theorem pair_history_minimum_liquidity {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace))
    (nonzero : pair ≠ 0) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes (initializedState factory domain token0 token1) steps finish ∧
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        ((∀ s ∈ steps, s.source.CallersNonzero) →
          finish.SupplyFloor ∧
          ∀ before after, (before, after) ∈ sourceReplayEdges
              (initializedState factory domain token0 token1) (steps.map PairStep.source) →
            before.SupplyFloor ∧ after.SupplyFloor ∧
              (0 < before.totalSupply.toNat → 1000 ≤ after.totalSupply.toNat)) :=
  pair_history_minimum_liquidity_from_checkpoint trace installed initial fresh
    (State.initialized_ledgerOn factory domain token0 token1).ledger
    (initialized_supplyFloor factory domain token0 token1) nonzero

/-- **Share value as a ratio, fee off, from the deployment checkpoint (U3).**  For a configured history
from the deployment checkpoint of a Pair not at address zero: if the authenticated answers of the
history's own steps satisfy `sourceReplayAnswers` (`EntryFeeOff` and `EntryNoShrink`, exactly as in
`pair_history_feeOff_product`), and no step or re-entered child has
caller zero, then every outermost replay boundary entered with positive supply leaves positive supply
(at least `MINIMUM_LIQUIDITY`), and `r0·r1/T² ≤ r0'·r1'/T'²` over `ℚ`: the squared share value
`√(r0·r1)/T` does not decrease across it. -/
theorem pair_history_feeOff_ratio {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace))
    (nonzero : pair ≠ 0) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes (initializedState factory domain token0 token1) steps finish ∧
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswers (initializedState factory domain token0 token1)
            (steps.map PairStep.source) →
          (∀ s ∈ steps, s.source.CallersNonzero) →
          ∀ before after, (before, after) ∈ sourceReplayEdges
              (initializedState factory domain token0 token1) (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            1000 ≤ after.totalSupply.toNat ∧
              ((before.reserve0.val * before.reserve1.val : ℚ) / (before.totalSupply.toNat : ℚ) ^ 2 ≤
                (after.reserve0.val * after.reserve1.val : ℚ) / (after.totalSupply.toNat : ℚ) ^ 2)) :=
  pair_history_feeOff_ratio_from_checkpoint trace installed initial fresh
    (State.initialized_ledgerOn factory domain token0 token1).ledger
    (initialized_supplyFloor factory domain token0 token1) nonzero

end Blanc.Lift.UniswapV2Pair
