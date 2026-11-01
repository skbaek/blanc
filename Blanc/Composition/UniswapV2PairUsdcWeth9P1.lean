import Blanc.Composition.UniswapV2PairUsdcOriginSeed
import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.GovernanceHistory

/-!
# The Pair's touched USDC allowance spenders

`PairUsdcAllowQuiet pair usdc trace` (`UniswapV2PairUsdcWeth9CheckpointF.lean`) is L1's
consumed premise P1: every allowance row of the Pair that the post-B trace touches reads
zero at B. This module names the finite spender population that premise ranges over
(`PairTouchedSpenders`, `pairTouchedSpenders`, `mem_pairTouchedSpenders`) and its historical
key representation (`pairTouchedHistoricalAllowanceKeys`). The derivation of P1 from the
original receipts is `UniswapV2PairUsdcRetainedP1.lean`.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc

/-- The spenders whose Pair allowance row the trace touches at `usdc`: membership in the
finite list `Usdc.historyTouchedKeys usdc trace`. -/
def PairTouchedSpenders (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (g : Adr) : Prop :=
  (Usdc.Key.allow pair g) ∈ Usdc.historyTouchedKeys usdc trace


/-- The exact finite spender population of `PairTouchedSpenders`, preserving duplicates
and order from the consumed post-checkpoint trace's touched-key list. -/
noncomputable def pairTouchedSpenders (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Adr :=
  (Usdc.historyTouchedKeys usdc trace).filterMap fun key =>
    match key with
    | .allow owner spender => if owner = pair then some spender else none
    | _ => none

theorem mem_pairTouchedSpenders {pair usdc spender : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    spender ∈ pairTouchedSpenders pair usdc trace ↔ PairTouchedSpenders pair usdc trace spender := by
  constructor
  · intro member
    obtain ⟨key, touched, selected⟩ := List.mem_filterMap.mp member
    cases key with
    | allow owner other =>
        change (if owner = pair then some other else none) = some spender at selected
        split at selected
        next equal =>
          subst owner
          cases selected
          exact touched
        next => cases selected
    | _ => cases selected
  · intro touched
    exact List.mem_filterMap.mpr ⟨.allow pair spender, touched, if_pos rfl⟩

/-- Historical key representation of precisely the allowance rows demanded by P1. -/
noncomputable def pairTouchedHistoricalAllowanceKeys (pair usdc : Adr) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    List HistoricalMappingKey :=
  (pairTouchedSpenders pair usdc trace).map (fun g => .modern (.allow pair g))

end Blanc.Composition.UniswapV2PairUsdcWeth9
