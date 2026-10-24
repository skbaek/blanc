import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.Usdc.SignedPaths
import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.StaticSilent
import Blanc.ExecutionMidHistoryInForest
import Blanc.Lift.Usdc.RetainedAllowanceWrites

/-! The Pair is excluded as owner on retained V2_2 permit frames after an actual cut. -/

namespace Blanc.Composition.UniswapV2PairUsdcOwners

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.ExecutionTrace

/-- An actual retained implementation permit frame after the cut cannot name the Pair as owner.
Library provenance uses the original full history; Pair installation starts at afterBenv. -/
theorem mid_retained_owner_excluded
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {pair P : Adr} {W : List UsdcDeployedEntry}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart P ((prior.step block).append later).rawNodes)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair) :
    ∀ (G : Exec.Frame), G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → G.sevm.code = Impl.code →
      Sevm.selector G.sevm ∈ selV2_2.owners → (Sevm.dataWord G.sevm 4).toAdr ≠ pair := by
  let full := (prior.step block).append later
  let mid := (MidHistoryTraceIn.tail block cut).append later
  have cap := BodyStageCapabilities.historical
  have bal : ∀ {f}, HistFork f → f.ruleSet.bal = none := fun h => h.bal_none
  have contexts := Usdc.ConfiguredHistoryTraceIn.usdc_ctxAt full cap bal world upgrades apartSlot
  have pairImages := mid.settled_codeImageIn UniswapV2Pair.pairSem pair cap
    (mid.rewardCreditsFunded cap) installed
    UniswapV2Pair.installedCert UniswapV2Pair.pairSem_image
  intro G member target code owners owner
  have fullMember := MidHistoryTraceIn.settledFrames_subset_full prior block cut later member
  have rawG := full.mem_rawFrames_of_mem_settledFrames G fullMember
  obtain ⟨pc, selected, hsg, entry, gas⟩ := full.rawFrame_entryFacts cap _ rawG
  obtain ⟨before, after, split⟩ := full.exists_rawNodes_split_of_mem_rawFrames rawG
  have earlier : ∀ b₁ n b₂, before = b₁ ++ n :: b₂ → CtxAt P W b₁ n := by
    intro b₁ n b₂ equal
    apply contexts b₁ n (b₂ ++ Exec.Frame.rootDeriv G :: after)
    rw [split, equal]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨-, held, -⟩ := world_at full cap world upgrades apartSlot split earlier
  have allowed := contexts before (Exec.Frame.rootDeriv G) after split P (Or.inl rfl) target
  obtain ⟨_, _, _, _, _, libCode⟩ := world.active_library_code allowed code held
  have pairCode : G.pre.getCode pair = UniswapV2Pair.code :=
    bytes_eq_of_image ((pairImages G member).trans UniswapV2Pair.pairSem_image)
  have neutral := selected.neutral
  have rejects : LibRejectsAt pair G.sevm :=
    LibRejectsH.at_of_neutral
      (LibSeam.lib_rejects_pairH UniswapV2Pair.not_staticAnswered_pairH) neutral
  obtain ⟨pcG, sevm, preG, out, run, committed⟩ := G
  change pcG = 0 at pc
  subst pcG
  cases out with
  | ok post =>
    exact impl_permit_pair_not_okH run code neutral entry.2 entry.1 gas
      libCode pairCode (notPre selected) rejects owners owner
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed

/-- Every actual retained tracked allowance write after the cut is non-increasing.
The original full-history R3 query population and R4 readiness premise are retained. -/
theorem mid_retainedRowWrite_nonInc
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {P pair : Adr} {Tr : Adr → Prop} {W : List UsdcDeployedEntry}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart P ((prior.step block).append later).rawNodes)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (proxyApart : ProxyRowsApart P pair Tr ((prior.step block).append later).rawNodes)
    (rowSep : UsdcRowSep P pair Tr ((prior.step block).append later).rawFrames)
    (initApart : InitRowsApart P pair Tr ((prior.step block).append later).rawFrames)
    (noCaller : ∀ (G : Exec.Frame),
      G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {R : Exec.Frame} (root : R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames ∧
      G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  have codes := ConfiguredHistoryTraceIn.usdc_nodeCodes
    ((prior.step block).append later) BodyStageCapabilities.historical
    (fun selected => selected.bal_none) world upgrades apartSlot
  obtain ⟨G, member, committed, chain, target, nonInc | residual⟩ :=
    MidHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner
      prior block cut later BodyStageCapabilities.historical
      (fun _ selected => selected.bal_none) codes proxyApart rowSep initApart
      noCaller excluded oldReady root retained found owner tracked
  · exact ⟨G, member, committed, chain, target, nonInc⟩
  · exact (mid_retained_owner_excluded prior block cut later world upgrades apartSlot
      installed notPre G member target residual.1 residual.2.1 residual.2.2).elim

end Blanc.Composition.UniswapV2PairUsdcOwners
