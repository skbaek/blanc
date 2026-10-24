import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.GovernanceHistory

/-!
# L1's P1 from the D→B USDC history

`PairUsdcAllowQuiet pair usdc trace` (`UniswapV2PairUsdcWeth9CheckpointF.lean`) is L1's
consumed premise P1: every allowance row of the Pair that the post-B trace touches reads
zero at B. `pairUsdcAllowQuiet_of_history` derives it from a historical-domain history from a
checkpoint `D` to `B` (the L3 history) through the Pair allowance law
`usdc_pairAllowance_noIncrease_deployed_apart` (`InitRowsHistory.lean`): on the spenders the
post-B trace touches (`PairTouchedSpenders`, a finite list), no tracked row rises from `D` to
`B`, so a zero seed at `D` stays zero at `B`.

The admin premise of that law comes from F2′ (`adminUpgradesWithinFrom_of_f2prime`,
`GovernanceHistory.lean`); `bal` and `capabilities` are discharged on `HistFork`. Every other
premise is a named hypothesis: the zero seed at `D` (`seedZero`) and the D→B premises of the
law. None is bundled.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc

/-- The spenders whose Pair allowance row the trace touches at `usdc`: membership in the
finite list `Usdc.historyTouchedKeys usdc trace`. -/
def PairTouchedSpenders (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (g : Adr) : Prop :=
  (Usdc.Key.allow pair g) ∈ Usdc.historyTouchedKeys usdc trace

/-- **P1 from the D→B history.** For a historical-domain history from `D` to `B` over the
deployed world at `D`, F2′ over its proxy entries with the deployment-before-upgrade order of
the F2′ implementations, the D→B premises of the Pair allowance law for the spenders the
post-B `trace` touches, and those rows zero at `D` (`seedZero`), the Pair's touched USDC
allowance rows read zero at `B`. -/
theorem pairUsdcAllowQuiet_of_history {pair usdc : Adr} {cfgH cfg : ChainConfig}
    {D B future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfgH D B)
    (trace : ConfiguredHistoryTrace cfg B future)
    {W : List UsdcDeployedEntry}
    (world : UsdcDeployedWorld history.BoundaryAt usdc W D.state)
    (governance : UsdcGovernanceF2primeEntries usdc history.rawFrames)
    (deployedFirst : UpgradeTargetsDeployedFirst usdc W)
    (apartSlot : ImplSlotApart usdc history.rawNodes)
    (slotsApart : ProxySlotsApart pair (PairTouchedSpenders pair usdc trace))
    (rowSep : UsdcRowSep usdc pair (PairTouchedSpenders pair usdc trace) history.rawFrames)
    (noPairException : NoPairExceptionWrites usdc pair (PairTouchedSpenders pair usdc trace)
      history.rawFrames history.rawNodes)
    (initApart : InitRowsApart usdc pair (PairTouchedSpenders pair usdc trace) history.rawFrames)
    (seedZero : ∀ g, PairTouchedSpenders pair usdc trace g →
      (D.state.getStor usdc).get (Usdc.allowSlot pair g) = 0) :
    PairUsdcAllowQuiet pair usdc trace := by
  intro g hg
  have bal : ∀ {fork}, HistFork fork → fork.ruleSet.bal = none := fun h => HistFork.bal_none h
  have law := (ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease_deployed_apart history
    BodyStageCapabilities.historical bal world
    (ConfiguredHistoryTraceIn.adminUpgradesWithinFrom_of_f2prime history
      BodyStageCapabilities.historical bal world governance deployedFirst)
    apartSlot slotsApart rowSep noPairException initApart ⟨g, hg, rfl⟩).2
  rw [seedZero g hg, B256.toNat_zero] at law
  exact B256.toNat_inj _ 0 ((Nat.le_zero.mp law).trans B256.toNat_zero.symm)

end Blanc.Composition.UniswapV2PairUsdcWeth9
