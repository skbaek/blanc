import Blanc.Composition.LiveUsdcWeth9B26213219History
import Blanc.ExecutionMidHistoryInForest

/-!
# WETH allowance provenance across the actual Pair deployment cut

The two deployment records must describe the same retained history. The link
below provides the intervening configured blocks and identifies the original
WETH history with their concatenation. Post-deployment caller provenance then
uses the already proved Pair child selectors. Separately, exact factory
execution proves that createPair preserves all WETH storage, with WETH's
installation derived from its earlier deployment. The older frame-based
prefix theorem remains available. `LiveUsdcWeth9B26213219AllowanceReplay`
composes storage preservation with replay on both sides of the creation cut.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The actual deployment transaction preserves WETH code and storage, including
every allowance slot. The installed-code premise concerns its entry state only. -/
theorem PairDeploymentTo.creation_preserves_weth {checkpoint : BlockChain}
    (d : PairDeploymentTo checkpoint)
    (installed : (d.cut.benv.state.getCode weth).toList ≠ []) :
    d.cut.afterBenv.state.getCode weth = d.cut.benv.state.getCode weth ∧
      d.cut.afterBenv.state.getStor weth = d.cut.benv.state.getStor weth := by
  have stat : d.cut.benv.stat = (initBenv d.block.fork d.pre d.block.block.header).stat :=
    d.cut.before.stat_eq
  have fork : mainnetChainConfig.forkAt 10008355 1588710145 = .ok d.cut.benv.stat.fork := by
    have selected := d.block.forkAt
    rw [d.number, d.time] at selected
    rw [stat]
    exact selected
  have stateGas : d.cut.benv.stat.rules.stateGas = none := by
    rw [stat]
    exact BodyStageCapabilities.historical.stateGas_none d.block.forkIn
  have valid : validateTransaction d.cut.benv.stat.rules d.cut.tx 0 =
      .ok (d.cut.head.intrinsicGas, d.cut.head.calldataFloorGasCost) :=
    (validateTransaction_sender_congr_none stateGas).trans d.cut.head.validation
  obtain ⟨post, bout, result, _, _, isolated⟩ :=
    UniswapV2Factory.pair_createPair_transaction_muirGlacier_effects fork
      d.txType d.data d.value d.nonce valid d.cut.head.checked d.funds d.gas d.gasBound
      d.factoryCode d.factoryNonce d.pairNonce d.pairCode d.slot2
  have same : post = d.cut.txState :=
    congrArg Prod.fst (Except.ok.inj (result.symm.trans d.cut.head.result))
  subst same
  exact isolated weth (by decide +kernel) (by decide +kernel) installed

/-- The actual Pair block and its continuation occur in the original WETH history. -/
structure DeploymentHistoryLink {checkpoint : BlockChain}
    (wd : WethDeploymentTo checkpoint) (pd : PairDeploymentTo checkpoint) where
  between : ConfiguredHistoryTraceIn HistFork mainnetChainConfig wd.completed pd.pre
  history : wd.history = (between.step pd.block).append pd.history

/-- The earlier WETH deployment and intervening actual history supply the
installed runtime at the entry to createPair; no extra checkpoint is assumed. -/
theorem DeploymentHistoryLink.weth_code_before_pair {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    some (pd.cut.benv.state.getCode weth).toList = Weth9.weth9Sem.image := by
  let spec := ContractSpecSem.ofStorageOnly Weth9.weth9Sem (fun _ => True)
  have preserves : spec.PreservesAdmittedIn HistFork weth (fun _ _ => True) :=
    fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩
  have created := Weth9.weth9_history_committed_from_creation_block wd.block wd.number wd.time
    wd.cut wd.txType wd.data wd.value wd.nonce wd.sender wd.funds wd.gas wd.gasBound wd.empty
  have start : spec.StateInv weth wd.cut.afterBenv.state := by
    refine ⟨?_, trivial, trivial⟩
    rw [weth_creation_address]
    exact congrArg some created.1
  let earlier := (MidHistoryTraceIn.tail wd.block wd.cut).append link.between
  have preInv : spec.StateInv weth pd.pre.state := earlier.stateInv_admitted_semIn
    preserves BodyStageCapabilities.historical
    ((earlier.frameAdmitted_iff_rawFrames weth _).2 fun _ _ _ => trivial)
    (earlier.rewardCreditsFunded BodyStageCapabilities.historical)
    start Weth9.installedCert rfl
  have fork : pd.block.fork = .muirGlacier := by
    have selected := pd.block.forkAt
    rw [pd.number, pd.time] at selected
    exact Except.ok.inj (selected.symm.trans UniswapV2Pair.pair_deployment_fork)
  have rules : (initBenv pd.block.fork pd.pre pd.block.block.header).stat.rules =
      Fork.ruleSet .muirGlacier := by
    change pd.block.fork.ruleSet = _
    rw [fork]
  have beacon := pd.block.bodyTrace.beacon.disabled_endpoints (by rw [rules]; rfl)
  have history := pd.block.bodyTrace.history.disabled_endpoints (by rw [rules]; rfl)
  have stateEq : pd.block.bodyTrace.historyState = pd.pre.state := history.1.trans beacon.1
  have beforeInv : spec.BenvInv weth
      (((initBenv pd.block.fork pd.pre pd.block.block.header).withState
        pd.block.bodyTrace.beaconState).withState pd.block.bodyTrace.historyState) := by
    refine ⟨?_, AdrSet.not_mem_empty⟩
    change spec.StateInv weth pd.block.bodyTrace.historyState
    rw [stateEq]
    exact preInv
  have bound : sum pd.block.bodyTrace.historyState.bal < 2 ^ 256 := by
    rw [stateEq]
    have total := pd.block.withdrawalsBound
    change sum pd.pre.state.bal + wdsum pd.block.block.wds < 2 ^ 256 at total
    omega
  have finalInv := pd.cut.before.benvInv_admitted_semIn preserves pd.block.forkIn
    (by change (initBenv pd.block.fork pd.pre pd.block.block.header).stat.rules.stateGas = none
        rw [rules]; rfl)
    ((pd.cut.before.frameAdmitted_iff_rawFrames weth _).2 fun _ _ _ => trivial)
    bound beforeInv Weth9.installedCert rfl
  exact finalInv.state.code

/-- The genuine creation cut preserves all WETH storage, with installation
derived from the original linked deployment histories. -/
theorem DeploymentHistoryLink.creation_preserves_weth {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    pd.cut.afterBenv.state.getStor weth = pd.cut.benv.state.getStor weth := by
  apply (pd.creation_preserves_weth ?_).2
  have code := link.weth_code_before_pair
  intro empty
  rw [empty] at code
  exact Weth9.weth9Sem.ne_nil rfl (Option.some.inj code.symm)

/-- Original retained frames through and including the genuine createPair transaction.
The post-createPair transaction suffix belongs to the later Pair trace instead. -/
def DeploymentHistoryLink.prefixFrames {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) : List Exec.Frame :=
  (MidHistoryTraceIn.tail wd.block wd.cut).settledFrames ++
    (link.between.settledFrames ++ pd.block.bodyTrace.beacon.settledFrames ++
      pd.block.bodyTrace.history.settledFrames ++ pd.cut.before.settledFrames ++
      pd.cut.head.settledFrames)

/-- This is an equality of the original retained derivations, not a new replay. -/
theorem DeploymentHistoryLink.frames_split {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    wd.trace.settledFrames = link.prefixFrames ++ pd.trace.settledFrames := by
  change ((MidHistoryTraceIn.tail wd.block wd.cut).append wd.history).settledFrames = _
  rw [MidHistoryTraceIn.append_settledFrames, link.history,
    MidHistoryTraceIn.settledFrames_cut_prefix link.between pd.block pd.cut pd.history]
  simp only [prefixFrames, PairDeploymentTo.trace, List.append_assoc]

/-- Later Pair frames retain membership in the original WETH execution. -/
theorem DeploymentHistoryLink.pairFrames_subset {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    pd.trace.settledFrames ⊆ wd.trace.settledFrames := by
  intro frame member
  rw [link.frames_split]
  exact List.mem_append_right _ member

/-- Restrict keylessness to the actual suffix without changing the full query population. -/
theorem DeploymentHistoryLink.pairQueries_subset {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    pd.trace.senderQueries ⊆ wd.trace.senderQueries := by
  intro query member
  change query ∈ ((MidHistoryTraceIn.tail wd.block wd.cut).append wd.history).senderQueries
  rw [MidHistoryTraceIn.append_senderQueries, link.history]
  exact List.mem_append_right _
    (MidHistoryTraceIn.senderQueries_subset_full link.between pd.block pd.cut pd.history member)

/-- After genuine Pair deployment, keylessness and the actual two contract images
exclude approve calls from the Pair to WETH. No selector premise remains on this suffix. -/
theorem DeploymentHistoryLink.afterPair_callerTarget {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair) :
    ∀ G ∈ pd.trace.settledFrames,
      CallerTarget pair weth (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3)
        G.sevm := by
  apply wd.callerTarget_of_senders_children pd.trace link.pairFrames_subset
    (pd.trace.noSenderAt_of_senderQueries
      (fun query member => excluded query (link.pairQueries_subset member)))
  exact pd.children_noApprove

/-- Only the pre-deployment interval and createPair transaction remain to classify.
The post-deployment half is discharged from the original histories and exact queries. -/
theorem DeploymentHistoryLink.noPairApproval_of_prefix {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (earlier : ∀ G ∈ link.prefixFrames,
      CallerTarget pair weth (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3)
        G.sevm) : wd.NoPairApproval := by
  apply wd.noPairApproval_of_callerTarget
  intro G member
  rw [link.frames_split] at member
  rcases List.mem_append.mp member with before | after
  · exact earlier G before
  · exact link.afterPair_callerTarget excluded G after

/-- Constructor-derived zero and the same original replay turn that split provenance
into all tracked Pair allowance rows being zero at the checkpoint. -/
theorem DeploymentHistoryLink.allowance_zero_of_prefix {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (earlier : ∀ G ∈ link.prefixFrames,
      CallerTarget pair weth (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3)
        G.sevm) :
    ∀ g, wd.keys (.allow pair g) →
      (checkpoint.state.getStor weth).get (Weth9.allowSlot pair g) = 0 :=
  wd.allowance_zero (link.noPairApproval_of_prefix excluded earlier)

end Blanc.Composition.LiveUsdcWeth9B26213219
