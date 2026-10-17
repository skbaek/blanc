import Blanc.Lift.UniswapV2Pair.PropertiesSides
import Blanc.Lift.UniswapV2Pair.ModelControls

/-! Per-side statement controls for C1 on actual reachable typed-model states.
`ModelControls.noShrink_required` shows the token0 half of the sync premise is needed. Here the
token1 half of sync and one half of burn are each shown load-bearing: on a state the production
driver reaches, only that half fails, the run succeeds, and the share-value product bound fails.
Evidence altitude: typed model, not EVM execution. -/

namespace Blanc.Lift.UniswapV2Pair.ModelControlsSides

open Jaune ModelControls

/-- The token1 balance answer is zero while the token0 answer backs its reserve. -/
def shrinking1Transcript : Transcript :=
  .next (answer 1002) .done (.next (answer 0) .done .done)

def shrinking1Run : RunResult := runTyped checkpoint context .sync shrinking1Transcript

/-- **Token1 sync control.**  From the reachable checkpoint, a real sync whose token1 answer
shrinks succeeds; its token0 half holds, its token1 half fails, and the product bound fails. -/
theorem noShrinkSide_one_required :
    donationRun.status = .success [] ∧ 0 < checkpoint.totalSupply.toNat ∧
    shrinking1Run.status = .success [] ∧
    SyncEntryNoShrinkSide .zero checkpoint shrinking1Transcript ∧
    ¬ SyncEntryNoShrinkSide .one checkpoint shrinking1Transcript ∧
    ¬ (checkpoint.reserve0.val * checkpoint.reserve1.val *
        shrinking1Run.frame.current.state.totalSupply.toNat ^ 2 ≤
      shrinking1Run.frame.current.state.reserve0.val *
        shrinking1Run.frame.current.state.reserve1.val * checkpoint.totalSupply.toNat ^ 2) := by
  rw [shrinking1Run, donation_execution.2]
  refine ⟨donation_execution.1, by decide, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · unfold SyncEntryNoShrinkSide
    decide +kernel
  · unfold SyncEntryNoShrinkSide
    decide +kernel

/-- `burn` whose token1 final balance answer is zero; every other answer is as in
`ModelControls.burnTranscript`. -/
def burnShrink1Transcript : Transcript :=
  .next (answer 1002) .done (.next (answer 1002) .done (.next (answer 0) .done
    (.next transferOk .done (.next transferOk .done
      (.next (answer 1001) .done (.next (answer 0) .done .done))))))

def burnShrink1Run : RunResult := runTyped burnReady context (.burn 20) burnShrink1Transcript

/-- **Burn control.**  After an actual LP transfer to the pair, a real burn whose token1 final
answer falls below the initial answer minus the payout succeeds; its token0 burn half holds, its
token1 burn half fails, and the product bound fails. -/
theorem burnNoShrinkSide_one_required :
    (runTyped checkpoint { context with sender := 20 } (.transfer 17 1) .done).status =
      .success (encodeWords [1]) ∧
    0 < burnReady.totalSupply.toNat ∧
    burnShrink1Run.status = .success (encodeWords [1, 1]) ∧
    BurnEntryNoShrinkSide .zero burnReady context.pair 20 burnShrink1Transcript ∧
    ¬ BurnEntryNoShrinkSide .one burnReady context.pair 20 burnShrink1Transcript ∧
    ¬ (burnReady.reserve0.val * burnReady.reserve1.val *
        burnShrink1Run.frame.current.state.totalSupply.toNat ^ 2 ≤
      burnShrink1Run.frame.current.state.reserve0.val *
        burnShrink1Run.frame.current.state.reserve1.val * burnReady.totalSupply.toNat ^ 2) := by
  rw [burnShrink1Run, burnReady, donation_execution.2]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, ?_⟩, ?_,
    by decide +kernel⟩
  · intro final0 answer0
    cases answer0
    decide +kernel
  · intro half
    obtain ⟨_, final⟩ := half
    exact absurd (final _ rfl) (by decide +kernel)

end Blanc.Lift.UniswapV2Pair.ModelControlsSides
