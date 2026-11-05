import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.Usdc.ProxyRetainedContextCodes
import Blanc.Composition.UsdcPair.SignedPaths
import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.StaticSilent
import Blanc.ExecutionMidHistoryInForest
import Blanc.ExecutionMidHistoryInNoDel
import Blanc.Lift.Usdc.RetainedAllowanceWrites

/-! The Pair is excluded as owner on retained V2_2 permit frames after an actual cut. -/

namespace Blanc.Composition.UniswapV2PairUsdcOwners

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.ExecutionTrace

/-- The Pair's installed code rejects the actual retained V2.2 permit path.
Library provenance is supplied internally by the old or retained context producer. -/
private theorem mid_retained_owner_excluded_of_library
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {pair P : Adr}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (library : ∀ G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames,
      G.sevm.currentTarget = P → G.sevm.code = Impl.code →
      G.pre.getCode usdcLib = Lib.code) :
    ∀ (G : Exec.Frame), G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → G.sevm.code = Impl.code →
      Sevm.selector G.sevm ∈ selV2_2.owners → (Sevm.dataWord G.sevm 4).toAdr ≠ pair := by
  let full := (prior.step block).append later
  let mid := (MidHistoryTraceIn.tail block cut).append later
  have cap := BodyStageCapabilities.historical
  have pairImages := mid.settled_codeImageIn UniswapV2Pair.pairSem pair cap
    (mid.rewardCreditsFunded cap) installed
    UniswapV2Pair.installedCert UniswapV2Pair.pairSem_image
  intro G member target code owners owner
  have fullMember := MidHistoryTraceIn.settledFrames_subset_full prior block cut later member
  have rawG := full.mem_rawFrames_of_mem_settledFrames G fullMember
  obtain ⟨pc, selected, _, entry, gas⟩ := full.rawFrame_entryFacts cap _ rawG
  have libCode := library G member target code
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

/-- Derive the V2.2 owner exclusion on the actual post-cut history from retained
runtime provenance. Library code at each implementation frame is a consequence
of the root context producer, not an additional final environmental premise. -/
theorem mid_retained_owner_excluded_from_installations_of_mid_roots
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {pair P : Adr} {W : List UsdcDeployedEntry}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (rootReady : ∀ R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots,
      R.pre.getCode P = Proxy.code ∧
        ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre)
    (governance : UsdcGovernanceF2primeOn P
      ((MidHistoryTraceIn.tail block cut).append later).settledFrames)
    (installations : ∀ R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots,
      ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
      write.value.toAdr ∈ F2prime.upgradeTargets →
      (N.devm.getCode write.value.toAdr).toList ≠ [] →
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm)
    (apartSlot : ∀ R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots,
      KnownImplSlotApart P (Exec.retainedNodes R.run))
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair) :
    ∀ (G : Exec.Frame), G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → G.sevm.code = Impl.code →
      Sevm.selector G.sevm ∈ selV2_2.owners → (Sevm.dataWord G.sevm 4).toAdr ≠ pair := by
  let full := (prior.step block).append later
  let mid := (MidHistoryTraceIn.tail block cut).append later
  apply mid_retained_owner_excluded_of_library prior block cut later installed notPre
  intro G member target code
  rw [mid.settledFrames_eq] at member
  obtain ⟨R, root, inRoot⟩ := List.mem_flatMap.mp member
  have ready := rootReady R root
  have rootGovernance : UsdcGovernanceF2primeOn P (Exec.committedFrames R.run) := by
    intro A committed
    apply governance A
    rw [mid.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, root, committed⟩
  have context := Usdc.ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_from_installations_of_root_governance
    full BodyStageCapabilities.historical (fun hf => hf.bal_none)
    (MidHistoryTraceIn.settledRoots_subset_full prior block cut later root)
    ready.1 impls lib ready.2 rootGovernance (installations R root) (apartSlot R root)
  have retained : Exec.Frame.rootDeriv G ∈ Exec.retainedNodes R.run :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run _).mpr
      ⟨G, inRoot, .refl _⟩
  rcases (context _ retained).2 target with ⟨proxy, _⟩ | ⟨e, _, actual, library⟩
  · exact (proxy_ne_impl (proxy.symm.trans code)).elim
  · exact library (actual.symm.trans code)

end Blanc.Composition.UniswapV2PairUsdcOwners
