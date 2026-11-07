import Blanc.ExecutionHistoryInEraBounds
import Blanc.ExecutionHistoryInFrameEnv
import Blanc.ExecutionHistoryInSystemEnvironment
import Blanc.ExecutionHistoryInSystemOpenings

/-!
# Histories that end before Cancun, and the gated authority premise

* `ConfiguredHistoryTraceIn.forksPreCancun_of_mainnet_tip` — a mainnet history whose tip is before
  Cancun selects a pre-Cancun fork at every block, by accepted-header chronology;
* `ConfiguredHistoryTraceIn.systemRawFrames_nil_of_preCancun` — such a history has no system frame;
* `ConfiguredHistoryTraceIn.precompileReadyPragueH` — `precompileReadyH` under the Prague-gated
  authority premise `PragueNoAuthorityAt`, which a pre-Prague history satisfies outright.

Contract-neutral.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- **A mainnet history ending before Cancun selects a pre-Cancun fork at every block.** -/
theorem ConfiguredHistoryTraceIn.forksPreCancun_of_mainnet_tip
    {F : Fork → Prop} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F mainnetChainConfig checkpoint future)
    {tip : Block} (last : future.blocks.getLast? = some tip)
    (early : tip.header.timestamp < mainnetCancunTimestamp) :
    history.ForksSatisfy PreCancun := by
  induction history generalizing tip with
  | refl => trivial
  | step prior block ih =>
    obtain ⟨_, _, _, ⟨parent, parentEq, parentLt⟩, postTip⟩ :=
      stateTransitionUsing_reachedStep block.transition
    have tipEq := Option.some.inj (postTip.symm.trans last)
    have blockEarly : block.block.header.timestamp < mainnetCancunTimestamp := by
      rw [tipEq]
      exact early
    exact ⟨ih parentEq (Nat.lt_trans parentLt blockEarly),
      mainnetChainConfig_preCancun_of_timestamp_lt block.forkAt blockEarly⟩

/-- **A pre-Cancun historical history has no system frame.** -/
theorem ConfiguredHistoryTraceIn.systemRawFrames_nil_of_preCancun
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (forks : history.ForksSatisfy PreCancun) : history.systemRawFrames = [] := by
  induction history with
  | refl => rfl
  | step prior block ih =>
    have hb := BeaconStageTrace.rawFrames_of_disabled block.bodyTrace.beacon
      (block.forkIn.sys_beaconRoots_false_of_preCancun forks.2)
    have hh := HistoryStageTrace.rawFrames_of_disabled block.bodyTrace.history
      (block.forkIn.sys_historyStorage_false_of_prePrague forks.2.toPrePrague)
    have hr := RequestStageTrace.rawFrames_of_disabled block.bodyTrace.requests
      (block.forkIn.header_requestsHash_false_of_prePrague forks.2.toPrePrague)
    change prior.systemRawFrames ++ (block.bodyTrace.beacon.rawFrames ++
      block.bodyTrace.history.rawFrames ++ block.bodyTrace.requests.rawFrames) = []
    rw [ih forks.1, hb, hh, hr]
    rfl

variable {a : Adr}

/-- `ConfiguredHistoryTraceIn.codeAt_empty_noStateGas` over historical forks, under the Prague-gated
authority premise. -/
theorem ConfiguredHistoryTraceIn.codeAt_empty_pragueNoAuthority
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (capabilities : BodyStageCapabilities HistFork)
    (hauth : history.PragueNoAuthorityAt a)
    (avoid : ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : checkpoint.state.getCode a = ByteArray.empty) :
    (∀ root ∈ history.txRawFrames, root.devm.getCode a = ByteArray.empty) ∧
      future.state.getCode a = ByteArray.empty := by
  induction history with
  | refl => exact ⟨fun root member => by simp only [txRawFrames, List.not_mem_nil] at member,
      hempty⟩
  | step prior block ih =>
      obtain ⟨hroots, hstate⟩ := ih hauth.1
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inl member))
      have hdis : block.fork.ruleSet.delegationEnabled = false ∨
          ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a := by
        by_cases hpre : PrePrague block.fork
        · exact Or.inl (block.forkIn.delegationDisabled_of_prePrague hpre)
        · exact Or.inr (hauth.2 hpre)
      obtain ⟨hroots', hfinal⟩ := block.codeAt_empty_noStateGas capabilities hdis
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ConfiguredHistoryTraceIn.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

/-- `precompileReadyH` under the Prague-gated authority premise. -/
theorem ConfiguredHistoryTraceIn.precompileReadyPragueH
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (capabilities : BodyStageCapabilities HistFork)
    (precompile : ∀ f, HistFork f → a ∈ (Fork.ruleSet f).precompiles)
    (checkpointEmpty : checkpoint.state.getCode a = ByteArray.empty)
    (noAuthority : trace.PragueNoAuthorityAt a)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.txRawFrames, getDelegatedCodeAddress (root.devm.getCode a) = none ∧
      a ∈ root.devm.accessedAddresses := by
  intro root member
  obtain ⟨hcode, -⟩ := trace.codeAt_empty_pragueNoAuthority capabilities noAuthority noFrame
    checkpointEmpty
  refine ⟨?_, trace.txRawFrames_warmIn capabilities precompile root member⟩
  have hnot : ¬ isValidDelegation ByteArray.empty := fun h => absurd h.1 (by decide)
  rw [hcode root member]
  simp only [getDelegatedCodeAddress, hnot, ↓reduceIte]

end ExecutionTrace

end Blanc
