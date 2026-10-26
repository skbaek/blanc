import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.GovernanceHistory
import Blanc.Composition.UniswapV2PairUsdcHistoryZeroIn

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

`pairUsdcAllowQuiet_of_mid_history` instead consumes the genuine transaction
cut and retained-root zero transport. It keeps the original full-history
world and exclusion populations and seeds the exact after-cut state. Its
full-history upgrade input is not a broader pre-deployment F2′ restriction.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc

/-- The spenders whose Pair allowance row the trace touches at `usdc`: membership in the
finite list `Usdc.historyTouchedKeys usdc trace`. -/
def PairTouchedSpenders (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (g : Adr) : Prop :=
  (Usdc.Key.allow pair g) ∈ Usdc.historyTouchedKeys usdc trace

/-- **P1 from the D→B history.** For a historical-domain history from `D` to `B` over the
deployed world at `D`, F2′ at its implementation-slot writes with the deployment-before-upgrade order of
the F2′ implementations, the D→B premises of the Pair allowance law for the spenders the
post-B `trace` touches, and those rows zero at `D` (`seedZero`), the Pair's touched USDC
allowance rows read zero at `B`. -/
theorem pairUsdcAllowQuiet_of_history {pair usdc : Adr} {cfgH cfg : ChainConfig}
    {D B future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfgH D B)
    (trace : ConfiguredHistoryTrace cfg B future)
    {W : List UsdcDeployedEntry}
    (world : UsdcDeployedWorld history.BoundaryAt usdc W D.state)
    (governance : UsdcGovernanceF2primeAtImplWrites usdc history.rawFrames history.rawNodes)
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

/-- **P1 from the genuine post-deployment cut.** The tracked rows are exactly
those touched by the consumed post-B trace. The original full-history world,
upgrades, sender/native-query populations and independent R4 premise are kept;
Pair installation and the initial zero seed refer to the actual selected
transaction's after-state. No block-end replacement, per-root zero or supplied
NoPairExceptionWrites premise is needed. Actual deployment-seed and freshness
discharge remain separate obligations of the complete historical instance. -/
theorem pairUsdcAllowQuiet_of_mid_history
    {cfgH cfg : ChainConfig} {checkpoint pre completed B future : BlockChain} {i : Nat}
    {usdc pair : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfgH checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfgH pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfgH completed B)
    (trace : ConfiguredHistoryTrace cfg B future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt usdc W checkpoint.state)
    (upgrades : UpgradesWithinFrom usdc W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart usdc ((prior.step block).append later).rawNodes)
    (apart : pair ≠ usdc)
    (senderExcluded : ∀ query ∈ ((prior.step block).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later)))
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (proxyApart : ProxyRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawNodes)
    (rowSep : UsdcRowSep usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawFrames)
    (initApart : InitRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawFrames)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) usdc pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = usdc →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (seedZero : ∀ g, PairTouchedSpenders pair usdc trace g →
      (cut.afterBenv.state.getStor usdc).get (allowSlot pair g) = 0) :
    PairUsdcAllowQuiet pair usdc trace := by
  intro g tracked
  exact UniswapV2PairUsdcOwners.mid_history_allowance_zero
    prior block cut later world upgrades apartSlot apart senderExcluded notSystem
    installed initial fresh notPre proxyApart rowSep initApart excluded oldReady
    tracked (seedZero g tracked)

end Blanc.Composition.UniswapV2PairUsdcWeth9
