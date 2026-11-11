import Blanc.LadderSem
import Blanc.ExecutionStagedBodyTrace
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistory
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionRewardCredits

/-!
# Exact balance credits in proof-of-work block rewards

The reward budget is a natural-number sum before any conversion to EVM words.
Beneficiaries may coincide. Every intermediate credit is justified by that same
budget; a bound on the final wrapped balance would not suffice. The same
budget discharges the per-credit `RewardCreditsFunded` premise of the historical
admitted-preservation theorems (`Blanc.ExecutionHistoricalAdmission`).
-/

namespace Blanc

open Jaune

/-! ## Bridge to the historical per-credit reward premise -/

namespace ExecutionTrace

/-- Every block of a retained history funds its reward credits; `stateGas = none`
comes per block from `BodyStageCapabilities F`. -/
theorem ConfiguredHistoryTraceIn.rewardCreditsFunded
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint : BlockChain} :
    {future : BlockChain} → (history : ConfiguredHistoryTraceIn F cfg checkpoint future) →
    BodyStageCapabilities F → history.RewardCreditsFunded
  | _, .refl _ _ _, _ => trivial
  | _, .step prior block, capabilities =>
      ⟨prior.rewardCreditsFunded capabilities,
        block.rewardCreditsFunded (capabilities.stateGas_none block.forkIn)⟩

end ExecutionTrace

end Blanc
