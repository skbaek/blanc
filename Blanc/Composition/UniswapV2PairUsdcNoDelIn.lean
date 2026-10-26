import Blanc.ExecutionMidHistoryInNoDel
import Blanc.Lift.Usdc.ProxyContextCodes

/-!
USDC proxy deletion exclusion for the original full history's genuine
after-Pair-cut replay. The existing full-world interface already installs the
proxy at its checkpoint; no extra code or deletion assumption is introduced.
-/

namespace Blanc.Composition.UniswapV2PairUsdcOwners

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.ExecutionTrace

/-- The actual USDC proxy is absent from every transaction deletion output
after the selected Pair deployment transaction. Safety is derived from the
same original full world, upgrades and implementation-slot separation.
This independent producer does not weaken the sender/native-query or scoped
R4 premises of the retained allowance-write consumer. -/
theorem mid_proxy_code_and_outputNotDeleted
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {P : Adr} {W : List UsdcDeployedEntry}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart P ((prior.step block).append later).rawNodes) :
    cut.afterBenv.state.getCode P = Proxy.code ∧
      ((MidHistoryTraceIn.tail block cut).append later).OutputNotDeleted P := by
  have cap := BodyStageCapabilities.historical
  have bal : ∀ {f}, HistFork f → f.ruleSet.bal = none := fun h => h.bal_none
  have proxy : UsdcContextCode Proxy.code := Or.inl rfl
  exact MidHistoryTraceIn.code_and_outputNotDeleted_of_full_safe proxy.not_delegation proxy.ne_nil
    prior block cut later cap world.proxy
    (usdc_safeRawFrames_of_world ((prior.step block).append later) cap bal world upgrades apartSlot)

/-- Deletion-only compatibility projection with the original premises. -/
theorem mid_proxy_outputNotDeleted
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {P : Adr} {W : List UsdcDeployedEntry}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart P ((prior.step block).append later).rawNodes) :
    ((MidHistoryTraceIn.tail block cut).append later).OutputNotDeleted P := by
  exact (mid_proxy_code_and_outputNotDeleted prior block cut later world upgrades apartSlot).2

end Blanc.Composition.UniswapV2PairUsdcOwners
