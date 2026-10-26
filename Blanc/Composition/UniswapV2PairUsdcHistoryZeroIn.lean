import Blanc.Composition.UniswapV2PairUsdcZeroIn
import Blanc.Composition.UniswapV2PairUsdcNoDelIn

/-!
# Allowance zero through the genuine post-deployment history

The original full history supplies proxy code, deletion exclusion and the
retained-root law. The existing settlement fold carries one actual after-cut
seed through the remaining transactions, body stages and later whole blocks.
-/

namespace Blanc.Composition.UniswapV2PairUsdcOwners

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.ExecutionTrace

/-- A tracked Pair allowance seeded at the actual settled-after transaction
boundary stays zero through its genuine suffix and later blocks. The original
full-history sender/native-query exclusions and the independent scoped R4
premise remain explicit. No per-root zero or cut-local proxy/deletion premise
is supplied. Establishing the actual deployment seed remains separate. -/
theorem mid_history_allowance_zero
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {P pair : Adr} {Tr : Adr → Prop} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart P ((prior.step block).append later).rawNodes)
    (apart : pair ≠ P)
    (senderExcluded : ∀ query ∈ ((prior.step block).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later)))
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (proxyApart : ProxyRowsApart P pair Tr ((prior.step block).append later).rawNodes)
    (rowSep : UsdcRowSep P pair Tr ((prior.step block).append later).rawFrames)
    (initApart : InitRowsApart P pair Tr ((prior.step block).append later).rawFrames)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {g : Adr} (tracked : Tr g)
    (zero : (cut.afterBenv.state.getStor P).get (allowSlot pair g) = 0) :
    (future.state.getStor P).get (allowSlot pair g) = 0 := by
  have proxy : UsdcContextCode Proxy.code := Or.inl rfl
  obtain ⟨code, notDeleted⟩ := mid_proxy_code_and_outputNotDeleted
    prior block cut later world upgrades apartSlot
  exact (((MidHistoryTraceIn.tail block cut).append later).cell_property_of_settledRoots
    (allowSlot pair g) (fun _ h => BodyStageCapabilities.historical.stateGas_none h)
    code proxy.ne_nil proxy.not_delegation notDeleted (fun value => value = 0)
    (fun R root incoming => mid_root_allowance_zero
      prior block cut later world upgrades apartSlot apart senderExcluded notSystem
      installed initial fresh notPre proxyApart rowSep initApart excluded oldReady
      root tracked incoming) zero).1

end Blanc.Composition.UniswapV2PairUsdcOwners
