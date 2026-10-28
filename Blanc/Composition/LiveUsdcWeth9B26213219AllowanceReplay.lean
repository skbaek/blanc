import Blanc.Composition.LiveUsdcWeth9B26213219AllowanceHistory
import Blanc.Lift.Weth9.ApprovalLogs
import Blanc.ExecutionHistoryReceiptLogs

/-!
# WETH allowance replay around genuine Pair creation

All segments use the original history's one tracked universe. The creation
transaction is joined by its proved storage equality, rather than by an
assumption about its retained callers or the value of an allowance.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- The original constructor footprint extended once by the full history's HASH-T. -/
theorem WethDeploymentTo.initial_foot {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint) :
    Weth9.FootInv d.keys (d.cut.afterBenv.state.getStor weth)
      (d.cut.afterBenv.state.bal weth) := by
  have created := Weth9.weth9_history_committed_from_creation_block d.block d.number d.time
    d.cut d.txType d.data d.value d.nonce d.sender d.funds d.gas d.gasBound d.empty
  rw [weth_creation_address]
  exact (created.2.2.1 _).extend d.fresh

/-- The same universe is admitted at every original raw WETH entry. -/
theorem WethDeploymentTo.entry_keys {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint) {root : Exec.Deriv}
    (member : root ∈ d.trace.rawFrames) (target : root.sevm.currentTarget = weth) :
    Weth9.footEntry d.keys root.sevm root.devm := by
  intro k touched
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨root, member, ?_⟩
  rw [target, ← weth_creation_address, ite_eq_left rfl]
  exact touched

/-- The original history before the Pair's deployment block. -/
def DeploymentHistoryLink.earlierTrace {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :=
  (MidHistoryTraceIn.tail wd.block wd.cut).append link.between

/-- Retained frames strictly before the actual createPair transaction. -/
def DeploymentHistoryLink.beforePairFrames {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) : List Exec.Frame :=
  link.earlierTrace.settledFrames ++ pd.cut.before.settledFrames

/-- Raw entries of the earlier mid-history, transaction prefix, creation and
later Pair trace all retain their membership in the original WETH history. -/
theorem DeploymentHistoryLink.raw_parts {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    link.earlierTrace.rawFrames ⊆ wd.trace.rawFrames ∧
      pd.cut.before.rawFrames ⊆ wd.trace.rawFrames ∧
      pd.cut.head.rawFrames ⊆ wd.trace.rawFrames ∧
      pd.trace.rawFrames ⊆ wd.trace.rawFrames := by
  have split : wd.trace.rawFrames =
      (MidHistoryTraceIn.tail wd.block wd.cut).rawFrames ++
        ((link.between.rawFrames ++ pd.block.bodyTrace.beacon.rawFrames ++
          pd.block.bodyTrace.history.rawFrames ++ pd.cut.before.rawFrames ++
          pd.cut.head.rawFrames) ++ pd.trace.rawFrames) := by
    change ((MidHistoryTraceIn.tail wd.block wd.cut).append wd.history).rawFrames = _
    rw [MidHistoryTraceIn.append_rawFrames, link.history,
      MidHistoryTraceIn.rawFrames_cut_prefix]
    rfl
  simp only [split, earlierTrace, MidHistoryTraceIn.append_rawFrames,
    List.subset_def, List.mem_append]
  exact ⟨fun {_} h => h.elim Or.inl
      (fun h => Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))),
    fun {_} h => Or.inr (Or.inl (Or.inl (Or.inr h))),
    fun {_} h => Or.inr (Or.inl (Or.inr h)), fun {_} h => Or.inr (Or.inr h)⟩

/-- The prefix replay ends at the actual pre-createPair storage and carries
the footprint needed to continue the same accounting proof. -/
theorem DeploymentHistoryLink.before_pair_replay {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    (Weth9.footSpec wd.keys).BenvInv weth pd.cut.benv ∧
      Weth9.LedgerReplay (Weth9.ledger wd.keys (wd.cut.afterBenv.state.getStor weth))
        (link.beforePairFrames.flatMap (Weth9.committedFrameInvocations weth))
        (Weth9.ledger wd.keys (pd.cut.benv.state.getStor weth)) := by
  have foot := wd.initial_foot
  let L := Weth9.weth9AccountingLadderIn HistFork HistFork.stateGas_none weth foot.inj
  have created := Weth9.weth9_history_committed_from_creation_block wd.block wd.number wd.time
    wd.cut wd.txType wd.data wd.value wd.nonce wd.sender wd.funds wd.gas wd.gasBound wd.empty
  have start : (Weth9.footSpec wd.keys).StateInv weth wd.cut.afterBenv.state := by
    apply Weth9.footSpec_stateInv_iff.mpr
    refine ⟨?_, created.2.2.2.1, foot.support, foot.backed⟩
    rw [weth_creation_address]
    exact congrArg some created.1
  have admitted : link.earlierTrace.FrameAdmitted weth (Weth9.footEntry wd.keys) :=
    (link.earlierTrace.frameAdmitted_iff_rawFrames weth _).2
      (fun _ member target => wd.entry_keys (link.raw_parts.1 member) target)
  have preInv := link.earlierTrace.stateInv_admitted_semIn L.preserves
    BodyStageCapabilities.historical admitted
    (link.earlierTrace.rewardCreditsFunded BodyStageCapabilities.historical)
    start Weth9.installedCert rfl
  obtain ⟨earlySteps, earlyReplay, earlyObserved⟩ := L.midHistoryIn link.earlierTrace
    admitted BodyStageCapabilities.historical
    (link.earlierTrace.rewardCreditsFunded BodyStageCapabilities.historical)
    start Weth9.installedCert rfl
  change earlySteps = link.earlierTrace.settledFrames.flatMap
    (Weth9.committedFrameInvocations weth) at earlyObserved
  subst earlySteps
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
  have txInv : (Weth9.footSpec wd.keys).StateInv weth pd.block.bodyTrace.historyState := by
    rw [stateEq]
    exact preInv
  have prefixAdmitted := (pd.cut.before.frameAdmitted_iff_rawFrames weth _).2
    (fun _ member target => wd.entry_keys (link.raw_parts.2.1 member) target)
  have bound : sum pd.block.bodyTrace.historyState.bal < 2 ^ 256 := by
    rw [stateEq]
    have total := pd.block.withdrawalsBound
    change sum pd.pre.state.bal + wdsum pd.block.block.wds < 2 ^ 256 at total
    omega
  have hsg : (initBenv pd.block.fork pd.pre pd.block.block.header).stat.rules.stateGas = none := by
    rw [rules]; rfl
  have cutInv := pd.cut.before.benvInv_admitted_semIn L.preserves pd.block.forkIn hsg
    prefixAdmitted bound ⟨txInv, AdrSet.not_mem_empty⟩ Weth9.installedCert rfl
  obtain ⟨prefixSteps, prefixReplay, prefixObserved⟩ := L.transactionListIn pd.cut.before
    prefixAdmitted txInv AdrSet.not_mem_empty bound pd.block.forkIn hsg
    Weth9.installedCert rfl pd.block.block.header.number
  change prefixSteps = pd.cut.before.settledFrames.flatMap
    (Weth9.committedFrameInvocations weth) at prefixObserved
  subst prefixSteps
  change Weth9.LedgerReplay (Weth9.ledger wd.keys (pd.block.bodyTrace.historyState.getStor weth))
    _ (Weth9.ledger wd.keys (pd.cut.benv.state.getStor weth)) at prefixReplay
  conv at prefixReplay => arg 1; rw [stateEq]
  refine ⟨cutInv, ?_⟩
  rw [beforePairFrames, List.flatMap_append]
  exact Weth9.LedgerReplay.append earlyReplay prefixReplay

/-- The constructor's zero allowance ledger remains zero when extended by
the original history's fresh tracked keys. -/
theorem WethDeploymentTo.initial_allow_zero {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint) :
    ∀ g, (Weth9.ledger d.keys (d.cut.afterBenv.state.getStor weth)).allow pair g = 0 := by
  have created := Weth9.weth9_history_committed_from_creation_block d.block d.number d.time
    d.cut d.txType d.data d.value d.nonce d.sender d.funds d.gas d.gasBound d.empty
  have same := Weth9.ledger_extend (created.2.2.1 0) d.fresh
  intro g
  rw [weth_creation_address]
  change (Weth9.ledger (Weth9.Key.extend (fun _ => False) _) _).allow pair g = 0
  exact (congrArg (fun l : Weth9.Ledger => l.allow pair g) same).trans
    (by
      change Weth9.trackedAllow (fun _ => False) _ pair g = 0
      exact Weth9.trackedAllow_of_not (fun impossible => impossible))

/-- The later replay starts from the actual pre-creation WETH ledger because
the genuine transaction preserves that storage. -/
theorem DeploymentHistoryLink.after_pair_replay {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    Weth9.LedgerReplay (Weth9.ledger wd.keys (pd.cut.benv.state.getStor weth))
      (pd.trace.settledFrames.flatMap (Weth9.committedFrameInvocations weth))
      (Weth9.ledger wd.keys (checkpoint.state.getStor weth)) := by
  have before := link.before_pair_replay.1
  let L := Weth9.weth9AccountingLadderIn HistFork HistFork.stateGas_none weth wd.initial_foot.inj
  have fork : HistFork pd.cut.benv.stat.fork := by
    rw [pd.cut.before.stat_eq]
    exact pd.block.forkIn
  have headAdmitted := (pd.cut.head.frameAdmitted_iff_rawFrames weth _).2
    (fun _ member target => wd.entry_keys (link.raw_parts.2.2.1 member) target)
  have after := pd.cut.head.benvInv_admitted_semIn L.preserves fork
    (HistFork.stateGas_none fork) headAdmitted
    (Weth9.footSpec_stateInv_iff.mp before.state).2.1 before Weth9.installedCert rfl
  have admitted := (pd.trace.frameAdmitted_iff_rawFrames weth _).2
    (fun _ member target => wd.entry_keys (link.raw_parts.2.2.2 member) target)
  obtain ⟨steps, replay, observed⟩ := L.midHistoryIn pd.trace admitted
    BodyStageCapabilities.historical (pd.trace.rewardCreditsFunded BodyStageCapabilities.historical)
    after.state Weth9.installedCert rfl
  change steps = pd.trace.settledFrames.flatMap (Weth9.committedFrameInvocations weth) at observed
  subst steps
  change Weth9.LedgerReplay (Weth9.ledger wd.keys (pd.cut.afterBenv.state.getStor weth))
    _ (Weth9.ledger wd.keys (checkpoint.state.getStor weth)) at replay
  conv at replay => arg 1; rw [link.creation_preserves_weth]
  exact replay

/-- The actual two-sided replay may omit createPair's identity effect on
WETH storage. Every retained invocation on either side remains in order. -/
theorem DeploymentHistoryLink.replay_without_creation {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    Weth9.LedgerReplay (Weth9.ledger wd.keys (wd.cut.afterBenv.state.getStor weth))
      ((link.beforePairFrames ++ pd.trace.settledFrames).flatMap
        (Weth9.committedFrameInvocations weth))
      (Weth9.ledger wd.keys (checkpoint.state.getStor weth)) := by
  rw [List.flatMap_append]
  exact link.before_pair_replay.2.append link.after_pair_replay

/-- Only frames strictly before createPair still need caller provenance.
The creation cut is handled by exact storage preservation, and the entire
later history by the actual Pair's proved child selectors and keylessness. -/
theorem DeploymentHistoryLink.allowance_zero_of_before_pair {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (earlier : ∀ G ∈ link.beforePairFrames,
      CallerTarget pair weth (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3)
        G.sevm) :
    ∀ g, wd.keys (.allow pair g) →
      (checkpoint.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  have zero := Weth9.replay_allow_zero link.replay_without_creation wd.initial_allow_zero ?_
  · intro g tracked
    have value := zero g
    change Weth9.trackedAllow wd.keys (checkpoint.state.getStor weth) pair g = 0 at value
    rwa [Weth9.trackedAllow_self tracked] at value
  · intro inv invMember caller
    obtain ⟨G, frameMember, selected⟩ := List.mem_flatMap.mp invMember
    unfold Weth9.committedFrameInvocations at selected
    split at selected
    · rename_i accepted
      have same := List.mem_singleton.mp selected
      subst inv
      have provenance : CallerTarget pair weth
          (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3) G.sevm := by
        rcases List.mem_append.mp frameMember with before | after
        · exact earlier G before
        · exact link.afterPair_callerTarget excluded G after
      exact provenance accepted.1 caller accepted.2.1
    · cases selected

open Blanc.Composition.UniswapV2PairUsdcWeth9 in
/-- The hybrid checkpoint consumes the derived zero allowances. Its only
remaining WETH caller obligation is strictly before genuine Pair creation. -/
theorem checkpoint_from_linked_histories {checkpoint : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (earlier : ∀ G ∈ link.beforePairFrames,
      CallerTarget pair weth (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3)
        G.sevm) :
    ∃ (st : UniswapV2Pair.State) (KP : UniswapV2Pair.WriterKey → Prop),
      JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys KP st
        checkpoint.state := by
  obtain ⟨st, KP, rep⟩ := pd.represented
  obtain ⟨sumNof, foot⟩ := wd.foot
  exact ⟨st, KP, checkpoint_of_history reads rep foot sumNof
    (reads.weth_tracked foot holderFresh) (link.allowance_zero_of_before_pair excluded earlier)⟩

/-- Every retained frame strictly before createPair belongs to the original
WETH deployment history, with the same code and entry capability evidence. -/
theorem DeploymentHistoryLink.beforePairFrames_subset {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    link.beforePairFrames ⊆ wd.trace.settledFrames := by
  intro frame member
  rw [link.frames_split]
  apply List.mem_append_left
  simp only [beforePairFrames, earlierTrace, MidHistoryTraceIn.append_settledFrames,
    List.mem_append] at member
  simp only [prefixFrames, List.mem_append]
  rcases member with (tail | middle) | before
  · exact Or.inl tail
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl middle))))
  · exact Or.inr (Or.inl (Or.inr before))

/-- Message roots over the same strict pre-createPair interval. Receipt
transport only needs each root's endpoint logs once. -/
def DeploymentHistoryLink.beforePairRoots {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) : List Exec.Frame :=
  link.earlierTrace.settledRoots ++ pd.cut.before.settledRoots

theorem DeploymentHistoryLink.beforePairFrames_eq {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    link.beforePairFrames = rootFrames link.beforePairRoots := by
  simp only [beforePairFrames, beforePairRoots, MidHistoryTraceIn.settledFrames_eq,
    ApplyTransactionsTrace.settledFrames_eq, rootFrames, List.flatMap_append]

/-- Absence at the actual root endpoints suffices for every retained child.
Complete settlement removes reverted descendants before this implication. -/
theorem DeploymentHistoryLink.noApprovalLogs_of_before_pair_roots
    {checkpoint : BlockChain} {wd : WethDeploymentTo checkpoint}
    {pd : PairDeploymentTo checkpoint} (link : DeploymentHistoryLink wd pd)
    (earlier : ∀ R ∈ link.beforePairRoots, ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉ R.post.logs) :
    ∀ G ∈ link.beforePairFrames, ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉ G.post.logs := by
  intro G member spender data event
  rw [link.beforePairFrames_eq] at member
  obtain ⟨R, rootMember, retained⟩ := List.mem_flatMap.mp member
  have selfMember : R ∈ link.beforePairFrames := by
    rw [link.beforePairFrames_eq]
    apply List.mem_flatMap.mpr
    refine ⟨R, rootMember, ?_⟩
    rw [Blanc.Exec.Frame.committedFrames_self]
    exact List.mem_cons_self
  have entry := wd.ownCode R (link.beforePairFrames_subset selfMember)
  exact earlier R rootMember spender data
    (Exec.committedFrame_logs_subset_noStateGas R.run R.committed entry.2.2.2.1
      G retained event)

/-- An alternative to pre-creation caller provenance: actual retained WETH
frames have no Approval event owned by the Pair. Creation itself preserves
storage; later approvals are excluded by the Pair's proved call restrictions.
The absence premise is evidence still to be supplied, not an adopted fact. -/
theorem DeploymentHistoryLink.allowance_zero_of_before_pair_noApprovalLogs
    {checkpoint : BlockChain} {wd : WethDeploymentTo checkpoint}
    {pd : PairDeploymentTo checkpoint} (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (earlier : ∀ G ∈ link.beforePairFrames, ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉ G.post.logs) :
    ∀ g, wd.keys (.allow pair g) →
      (checkpoint.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  have zero := Weth9.Ledger.run_allow_zero_of_noApprove
    link.replay_without_creation wd.initial_allow_zero ?_
  · intro g tracked
    have value := zero g
    change Weth9.trackedAllow wd.keys (checkpoint.state.getStor weth) pair g = 0 at value
    rwa [Weth9.trackedAllow_self tracked] at value
  · intro call member spender amount same
    obtain ⟨inv, invMember, decoded⟩ := List.mem_filterMap.mp member
    rw [same] at decoded
    obtain ⟨G, frameMember, selected⟩ := List.mem_flatMap.mp invMember
    unfold Weth9.committedFrameInvocations at selected
    split at selected
    · rename_i accepted
      have sameInv := List.mem_singleton.mp selected
      subst inv
      rcases List.mem_append.mp frameMember with before | after
      · have entry := wd.ownCode G (link.beforePairFrames_subset before)
        obtain ⟨data, event⟩ := Weth9.approval_log_of_frame G entry.2.1
          (entry.2.2.2.2 accepted.1) entry.2.2.2.1 decoded
        rw [accepted.1] at event
        exact earlier G before spender data event
      · obtain ⟨caller, selector⟩ := Weth9.decodeCall_approve_source decoded
        exact link.afterPair_callerTarget excluded G after accepted.1 caller accepted.2.1 selector
    · cases selected

open Blanc.Composition.UniswapV2PairUsdcWeth9 in
/-- The same live checkpoint accepts the pre-createPair log-absence route.
No finite storage sample substitutes for the original retained history. -/
theorem checkpoint_from_linked_histories_noApprovalLogs {checkpoint : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (earlier : ∀ G ∈ link.beforePairFrames, ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉ G.post.logs) :
    ∃ (st : UniswapV2Pair.State) (KP : UniswapV2Pair.WriterKey → Prop),
      JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys KP st
        checkpoint.state := by
  obtain ⟨st, KP, rep⟩ := pd.represented
  obtain ⟨sumNof, foot⟩ := wd.foot
  exact ⟨st, KP, checkpoint_of_history reads rep foot sumNof
    (reads.weth_tracked foot holderFresh)
    (link.allowance_zero_of_before_pair_noApprovalLogs excluded earlier)⟩

/-- Actual original receipts strictly after WETH creation and strictly before
the genuine Pair-creation transaction, including both partial boundary blocks. -/
def DeploymentHistoryLink.beforePairReceiptLogs {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) : List Log :=
  wd.block.receiptLogsBetween (wd.index + 1) wd.block.bodyTrace.decodedTxs.length ++
    link.between.receiptLogs ++ pd.block.receiptLogsBetween 0 38

/-- The canonical original-index receipt interval supplies the root predicate.
The actual Pair deployment date discharges the system-stage era condition. -/
theorem DeploymentHistoryLink.noApprovalLogs_of_before_pair_receipts
    {checkpoint : BlockChain} {wd : WethDeploymentTo checkpoint}
    {pd : PairDeploymentTo checkpoint} (link : DeploymentHistoryLink wd pd)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs) :
    ∀ G ∈ link.beforePairFrames, ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉ G.post.logs := by
  have early : pd.block.block.header.timestamp < mainnetCancunTimestamp := by
    rw [pd.time]
    decide +kernel
  have covered := ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_receipts
    wd.block wd.cut link.between pd.block pd.cut early
    (fun entry => ∀ (spender : Adr) (data : Bytes),
      entry ≠ Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data) (by
        intro entry member spender data same
        subst entry
        exact logs spender data member)
  apply link.noApprovalLogs_of_before_pair_roots
  intro root member spender data event
  have inInterval : root ∈ link.earlierTrace.settledRoots ++
      pd.block.rootsBeforeTxSplit pd.cut := by
    rcases List.mem_append.mp member with first | last
    · exact List.mem_append_left _ first
    · exact List.mem_append_right _ (List.mem_append_right _ last)
  exact covered root inInterval _ event spender data rfl

open Blanc.Composition.UniswapV2PairUsdcWeth9 in
/-- The hybrid checkpoint and future factory premises from the original
strict receipt interval. Receipt absence remains a named evidence obligation;
no unproved prior-incarnation exclusion or final allowance value is supplied. -/
theorem checkpoint_from_linked_receipts {checkpoint : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs) :
    ∃ (st : UniswapV2Pair.State) (KP : UniswapV2Pair.WriterKey → Prop),
      JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys KP st
        checkpoint.state ∧
      some (checkpoint.state.getCode st.factory).toList = UniswapV2Factory.factorySem.image ∧
      st.factory ≠ systemAddress := by
  obtain ⟨st, KP, joint⟩ := checkpoint_from_linked_histories_noApprovalLogs reads wd pd link
    holderFresh excluded (link.noApprovalLogs_of_before_pair_receipts logs)
  exact ⟨st, KP, joint, reads.factory_facts joint.weth9.pairRep⟩

open Blanc.Composition.UniswapV2PairUsdcWeth9 in
/-- Fix the historical Pair witness once, so future freshness premises and
outcomes refer to the same represented model and key universe. -/
theorem checkpoint_at_deployment_model {checkpoint : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys pd.keys
      pd.model checkpoint.state := by
  obtain ⟨sumNof, foot⟩ := wd.foot
  exact checkpoint_of_history reads pd.rep foot sumNof
    (reads.weth_tracked foot holderFresh)
    (link.allowance_zero_of_before_pair_noApprovalLogs excluded
      (link.noApprovalLogs_of_before_pair_receipts logs))

end Blanc.Composition.LiveUsdcWeth9B26213219
