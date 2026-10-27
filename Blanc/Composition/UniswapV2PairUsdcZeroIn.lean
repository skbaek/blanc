import Blanc.Composition.UniswapV2PairUsdcCallersIn
import Blanc.Composition.UniswapV2PairUsdcOwnersIn
import Blanc.ExecutionRetainedCellZero

/-!
Zero preservation in each actual retained root after the Pair deployment cut.
The root law is conditional on its own incoming cell, for history transport.
-/

namespace Blanc.Composition.UniswapV2PairUsdcOwners

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.ExecutionTrace

/-- An actual retained root preserves an initially zero tracked allowance cell.
The original full history supplies native-query exclusion and R4; sender
exclusion is needed only on the actual post-cut queries.
the Pair's installed state and replay begin at the genuine after-cut boundary.
Root code and caller exclusion are derived, not supplied independently. -/
theorem mid_root_allowance_zero_of_rawClass
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
    (senderExcluded : ∀ query ∈ ((MidHistoryTraceIn.tail block cut).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later)))
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (rawClass : UsdcRawRowWriteClass P pair Tr
      ((prior.step block).append later).rawFrames ((prior.step block).append later).rawNodes)
    (initApart : InitRowsApart P pair Tr ((prior.step block).append later).rawFrames)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {R : Exec.Frame} (root : R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots)
    {g : Adr} (tracked : Tr g)
    (zero : (R.pre.getStor P).get (allowSlot pair g) = 0) :
    (R.post.getStor P).get (allowSlot pair g) = 0 := by
  let full := (prior.step block).append later
  let mid := (MidHistoryTraceIn.tail block cut).append later
  have cap := BodyStageCapabilities.historical
  have bal : ∀ {f}, HistFork f → f.ruleSet.bal = none := fun h => h.bal_none
  have member : R ∈ mid.settledFrames := by
    rw [mid.settledFrames_eq]
    apply List.mem_flatMap.mpr
    refine ⟨R, root, ?_⟩
    rw [Blanc.Exec.Frame.committedFrames_self R]
    exact List.mem_cons_self
  have fullMember := MidHistoryTraceIn.settledFrames_subset_full prior block cut later member
  have raw := full.mem_rawFrames_of_mem_settledFrames R fullMember
  have code : R.pre.getCode P = Proxy.code :=
    rawFrame_proxyCode_of_world full cap bal world upgrades apartSlot
      (Exec.Frame.rootDeriv R) raw
  have hcode : (R.pre.getCode P).toList ≠ [] := by
    rw [code]
    exact (UsdcContextCode.ne_nil (Or.inl rfl : UsdcContextCode Proxy.code))
  have facts := full.rawFrame_entryFacts cap (Exec.Frame.rootDeriv R) raw
  have noCaller := UniswapV2PairUsdcCallers.mid_retained_caller_write_excluded_of_mid_senderQueries
    prior block cut later world upgrades apartSlot apart senderExcluded notSystem
    installed initial fresh
  apply Exec.cell_zero_of_retained_nonInc_noStateGas R.run R.committed facts.2.2.1 hcode
  · intro m retained w found owner key
    obtain ⟨_, _, _, _, _, bound⟩ := mid_retainedRowWrite_nonInc_of_rawClass
      prior block cut later world upgrades apartSlot installed notPre rawClass
      initApart noCaller excluded oldReady root retained found owner
      ⟨g, tracked, key.symm⟩
    simpa only [key] using bound
  · exact zero

/-- An actual retained root preserves an initially zero tracked allowance cell.
The original full history supplies native-query exclusion and R4; sender
exclusion is needed only on the actual post-cut queries.
the Pair's installed state and replay begin at the genuine after-cut boundary.
Root code and caller exclusion are derived, not supplied independently. -/
theorem mid_root_allowance_zero_of_mid_senderQueries
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
    (senderExcluded : ∀ query ∈ ((MidHistoryTraceIn.tail block cut).append later).senderQueries,
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
    {R : Exec.Frame} (root : R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots)
    {g : Adr} (tracked : Tr g)
    (zero : (R.pre.getStor P).get (allowSlot pair g) = 0) :
    (R.post.getStor P).get (allowSlot pair g) = 0 := by
  have codes := ConfiguredHistoryTraceIn.usdc_nodeCodes
    ((prior.step block).append later) BodyStageCapabilities.historical
    (fun selected => selected.bal_none) world upgrades apartSlot
  exact mid_root_allowance_zero_of_rawClass
    prior block cut later world upgrades apartSlot apart senderExcluded notSystem
    installed initial fresh notPre
    (ConfiguredHistoryTraceIn.usdc_rawRowWrite ((prior.step block).append later)
      BodyStageCapabilities.historical codes proxyApart rowSep)
    initApart excluded oldReady root tracked zero

/-- Compatibility with full-history sender exclusion. -/
theorem mid_root_allowance_zero
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
    {R : Exec.Frame} (root : R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots)
    {g : Adr} (tracked : Tr g)
    (zero : (R.pre.getStor P).get (allowSlot pair g) = 0) :
    (R.post.getStor P).get (allowSlot pair g) = 0 := by
  exact mid_root_allowance_zero_of_mid_senderQueries
    prior block cut later world upgrades apartSlot apart
    (fun query member => senderExcluded query
      (MidHistoryTraceIn.senderQueries_subset_full prior block cut later member))
    notSystem installed initial fresh notPre proxyApart rowSep initApart excluded oldReady
    root tracked zero

end Blanc.Composition.UniswapV2PairUsdcOwners
