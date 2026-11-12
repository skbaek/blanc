import Blanc.ListChunks
import Blanc.Composition.DepositClassified
import Blanc.Lift.BeaconDeposit.RequestCodec
import Blanc.Composition.DepositRequests
import Blanc.Composition.DepositLedgerFate

/-! Positional execution/consensus deposit joins and the original request seam controls. -/
namespace Blanc.Composition.DepositJoint

open Jaune JauneConsensus Blanc Blanc.ExecutionTrace Blanc.ConsensusSsz
open Blanc.Corpus.Freeze.Deposit
open Blanc.Lift.BeaconDeposit
open Blanc.Lift.BeaconDeposit.RequestCodec
open private tagged appliedEntries requestEntries ledgerRun ingressFacts sourceTags from Blanc.Composition.DepositLedgerFate

/-- A successful joint step cannot accept requests different from its own executed body. -/
theorem deliveryControl : D9DeliveryControl := by
  intro P cfg ccfg bls s b req f st bout converted resolved executed different post accepted
  obtain ⟨_, actualReq, actualConverted, engine⟩ := Blanc.jointStep_engine accepted
  obtain rfl : actualReq = req := Except.ok.inj (actualConverted.symm.trans converted)
  obtain ⟨_, _, _, _, actualFork, actualResolved, _, _, _, actualState, actualOutput,
    actualExecuted, requests⟩ := engineVerdict_ok_iff.mp engine
  obtain rfl : actualFork = f := Except.ok.inj (actualResolved.symm.trans resolved)
  have same : (actualState, actualOutput) = (st, bout) :=
    Except.ok.inj (actualExecuted.symm.trans executed)
  cases same
  exact different requests

/-- A mismatched request list fails at `requestsHash` when hashes differ, or at `requestsMismatch`
under a hypothetical hash collision. -/
theorem deliverySeamControl : D9DeliverySeamControl := by
  intro P cfg cf exec req f st bout
  dsimp only
  intro forks nonempty blockHash hashes chain fork paired size header body checks different
  have rules : f.ruleSet.pow = none ∧ f.ruleSet.header.requestsHash = true ∧
      f.ruleSet.bal = none := by
    rcases forks with rfl | rfl <;> cases f <;> cases paired <;> exact ⟨rfl, rfl, rfl⟩
  have ommers : (payloadToBlock req).ommers = [] := rfl
  have ommersOk : checkBlockOmmersScheduledE cfg f.ruleSet exec
      (payloadToBlock req).header (payloadToBlock req).ommers = .ok () := by
    rw [checkBlockOmmersScheduledE, rules.1, ommers]
    rfl
  have commitment : (payloadToBlock req).header.requestsHash =
      some (computeRequestsHash req.executionRequests) := rfl
  have n1 : ¬(req.executionPayload.txBytes.any List.isEmpty = true) := by
    simp only [nonempty, Bool.false_eq_true, not_false_eq_true]
  have n2 : ¬(((payloadToBlock req).header.hash != req.executionPayload.block_hash) = true) := by
    simp only [blockHash, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]
  have n3 : ¬((req.versionedHashes != req.versionedHashes) = true) := by
    simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]
  have n4 : ¬((f.consensusFork? != some cf) = true) := by
    simp only [paired, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]
  have n5 : (bout.requests != req.executionRequests) = true := by
    simpa only [bne_iff_ne] using different
  unfold stateTransitionChecks at checks
  have g1 : ¬(max bout.blockGasUsed bout.blockStateGasUsed ≠ (payloadToBlock req).header.gasUsed) := by
    intro bad; rw [ite_eq_left bad] at checks; cases checks
  rw [ite_eq_right g1] at checks
  have g2 : ¬(getTransactionsRoot bout ≠ (payloadToBlock req).header.txsRoot) := by
    intro bad; rw [ite_eq_left bad] at checks; cases checks
  rw [ite_eq_right g2] at checks
  have g3 : ¬(st.root ≠ (payloadToBlock req).header.stateRoot) := by
    intro bad; rw [ite_eq_left bad] at checks; cases checks
  rw [ite_eq_right g3] at checks
  have g4 : ¬(getReceiptRoot bout ≠ (payloadToBlock req).header.receiptRoot) := by
    intro bad; rw [ite_eq_left bad] at checks; cases checks
  rw [ite_eq_right g4] at checks
  have g5 : ¬(logsBloom bout.blockLogs ≠ (payloadToBlock req).header.bloom) := by
    intro bad; rw [ite_eq_left bad] at checks; cases checks
  rw [ite_eq_right g5] at checks
  have g6 : ¬((payloadToBlock req).header.withdrawalsRoot.any (· != getWithdrawalsRoot bout) = true) := by
    intro bad; rw [ite_eq_left bad] at checks; cases checks
  rw [ite_eq_right g6] at checks
  have g7 : ¬((payloadToBlock req).header.blobGasUsed.any (· != bout.blobGasUsed) = true) := by
    intro bad; rw [ite_eq_left bad] at checks; cases checks
  rw [ite_eq_right g7] at checks
  constructor
  · intro hashDifferent
    have requestCheck : ∃ msg, stateTransitionChecks bout (payloadToBlock req).header
        (getTransactionsRoot bout) st.root (getReceiptRoot bout) (logsBloom bout.blockLogs)
        (getWithdrawalsRoot bout) (some (computeRequestsHash bout.requests)) =
          .error (.requestsHash msg) := by
      unfold stateTransitionChecks
      rw [ite_eq_right g1, ite_eq_right g2, ite_eq_right g3, ite_eq_right g4,
        ite_eq_right g5, ite_eq_right g6, ite_eq_right g7]
      have bad : some (computeRequestsHash bout.requests) ≠
          (payloadToBlock req).header.requestsHash := by
        rw [commitment]
        exact fun h => hashDifferent (Option.some.inj h)
      rw [ite_eq_left bad]
      exact ⟨_, rfl⟩
    obtain ⟨msg, requestCheck⟩ := requestCheck
    have transition : stateTransitionScheduledE cfg f exec (payloadToBlock req) =
        .ok (.error (.block (.requestsHash msg))) := by
      simp only [stateTransitionScheduledE, stateTransitionCoreE, header, Except.mapError,
        bind, Except.bind, ommersOk, body, rules.2.1, ↓reduceIte, requestCheck]
      rfl
    refine ⟨msg, ?_⟩
    unfold engineVerdict
    rw [ite_eq_right n1, ite_eq_right n2]
    simp only [hashes, Except.mapError, bind, Except.bind]
    rw [ite_eq_right n3]
    simp only [chain, fork]
    rw [ite_eq_right n4]
    simp only [size, transition]
    rfl
  · intro hashSame
    have requestCheck : stateTransitionChecks bout (payloadToBlock req).header
        (getTransactionsRoot bout) st.root (getReceiptRoot bout) (logsBloom bout.blockLogs)
        (getWithdrawalsRoot bout) (some (computeRequestsHash bout.requests)) = .ok () := by
      unfold stateTransitionChecks
      rw [ite_eq_right g1, ite_eq_right g2, ite_eq_right g3, ite_eq_right g4,
        ite_eq_right g5, ite_eq_right g6, ite_eq_right g7]
      rw [hashSame, ← commitment]
      rw [ite_eq_right (fun h => h rfl)]
      rfl
    have transition : stateTransitionScheduledE cfg f exec (payloadToBlock req) =
        .ok (.ok ⟨appendBlock exec.blocks (payloadToBlock req), st, exec.chainId⟩) := by
      simp only [stateTransitionScheduledE, stateTransitionCoreE, header, Except.mapError,
        bind, Except.bind, ommersOk, body, rules.2.1, ↓reduceIte, requestCheck,
        blockAccessListCheck, rules.2.2]
      rfl
    unfold engineVerdict
    rw [ite_eq_right n1, ite_eq_right n2]
    simp only [hashes, Except.mapError, bind, Except.bind]
    rw [ite_eq_right n3]
    simp only [chain, fork]
    rw [ite_eq_right n4]
    simp only [size, transition, body]
    change (if (bout.requests != req.executionRequests) = true then
      Except.error EngineReject.requestsMismatch else
      .ok (BlockChain.mk (appendBlock exec.blocks (payloadToBlock req)) st exec.chainId)) = _
    rw [ite_eq_left n5]

private noncomputable def fullDeployment {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    BeaconDeploymentTo final.exec :=
  { v.deployment with
    modern := v.ingress.toExec (concatConfiguredHistory v.deployment.modern v.pre)
    modernSystemNoAuthority := v.systemNoAuthority
    modernNoAuthority := v.noAuthority
    modernNoFrame := v.noFrame }

private theorem fullTrace_leaves {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    ∀ fr ∈ v.fullTrace.settledFrames, fr.sevm.currentTarget = depositAddr →
      Exec.descendantFrames fr.run = [] := by
  intro fr member target
  obtain ⟨idx, lookup⟩ := List.mem_iff_getElem?.mp member
  have lookup2 : (fullDeployment v).trace.settledFrames[idx]? = some fr := lookup
  obtain ⟨pc, fork, image, fresh, _, sha, _⟩ :=
    (fullDeployment v).classification_inputs idx fr lookup2 target
  rcases fr with ⟨fpc, sevm, pre, out, run, committed⟩
  cases out with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    dsimp only at pc fork image fresh sha ⊢
    subst fpc
    exact target_descendantFrames_nilH run image fork fresh sha

private theorem prague_depositCode {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    DepositCodeAt v.deployment.P.state := by
  let d := v.deployment
  let historical := (d.dc.step d.first).append d.tail
  have initial : beaconSpec.StateInv Creation.depositAddress d.D.state :=
    ⟨by rw [d.deployed.1]; rfl, trivial, ⟨[], d.deployed.2⟩⟩
  have rewards := historical.rewardCreditsFunded BodyStageCapabilities.historical
  obtain ⟨_, atPrague, _⟩ := configuredHistoryIn_environment historical
    (d.anchors.historicalOpenings d.dc d.first d.tail)
    (fun p _ => d.anchors.historicalPragueNoAuthorityAt d.dc d.first d.tail p.1)
    d.checkpointEmpty (d.anchors.historicalPragueNoAuthorityAt d.dc d.first d.tail 2)
    d.historicalNoFrame rewards initial
  exact ContractSpecSem.StateInv.getCode_eq_of_image (C := code) rfl atPrague

private theorem settledFrames_appendIn {F : Jaune.Fork → Prop} {cfg : ChainConfig}
    {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) :
    (first.append second).settledFrames = first.settledFrames ++ second.settledFrames := by
  induction second with
  | refl => simp only [ConfiguredHistoryTraceIn.append, ConfiguredHistoryTraceIn.settledFrames, List.append_nil]
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.append, ConfiguredHistoryTraceIn.settledFrames, ih, List.append_assoc]

private theorem concatConfiguredHistory_settledFrames {cfg : ChainConfig} {A B C : BlockChain}
    (ab : ConfiguredHistoryTrace cfg A B) (bc : ConfiguredHistoryTrace cfg B C) :
    (concatConfiguredHistory ab bc).settledFrames = ab.settledFrames ++ bc.settledFrames := by
  induction bc with
  | refl => simp only [concatConfiguredHistory, ConfiguredHistoryTrace.settledFrames, List.append_nil]
  | step prior block ih =>
    simp only [concatConfiguredHistory, ConfiguredHistoryTrace.settledFrames, ih, List.append_assoc]

private theorem toExec_settled_run {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s0 s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s0.exec)
    (run : JointRun cfg ccfg bls s0 s) :
    (run.toExec pre).settledFrames =
      pre.settledFrames ++ run.steps.flatMap (fun D => D.stepTrace.trace.settledFrames) := by
  induction run with
  | nil => simp only [JointRun.toExec_nil, JointRun.steps_nil, List.flatMap_nil, List.append_nil]
  | snoc run b step bound ih =>
    simp only [JointRun.toExec_snoc, JointRun.steps_snoc, ConfiguredHistoryTrace.settledFrames,
      List.flatMap_append, List.flatMap_singleton, ih, List.append_assoc]

private theorem toExec_settled_ingress {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec)
    (ingress : JointRunIngress cfg ccfg bls anchor final) :
    (ingress.toExec pre).settledFrames =
      pre.settledFrames ++ ingress.steps.flatMap (fun D => D.stepTrace.trace.settledFrames) := by
  cases ingress with
  | standard run => exact toExec_settled_run pre run
  | atElectraSlot _ _ _ _ firstStep firstBound tail =>
    simp only [JointRunIngress.toExec, JointRunIngress.steps, toExec_settled_run,
      ConfiguredHistoryTrace.settledFrames, List.flatMap_cons, List.append_assoc]

private theorem anchorTrace_settledFrames {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    v.anchorTrace.settledFrames = v.deployment.trace.settledFrames ++ v.pre.settledFrames := by
  simp only [DepositJoint.anchorTrace, BeaconDeploymentTo.trace, settledFrames_appendIn,
    ConfiguredHistoryTrace.toHistForkIn_settledFrames, concatConfiguredHistory_settledFrames,
    List.append_assoc]

private theorem fullTrace_settledFrames {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    v.fullTrace.settledFrames =
      v.anchorTrace.settledFrames ++
        v.ingress.steps.flatMap (fun D => D.stepTrace.trace.settledFrames) := by
  simp only [DepositJoint.fullTrace, DepositJoint.anchorTrace, settledFrames_appendIn,
    ConfiguredHistoryTrace.toHistForkIn_settledFrames, toExec_settled_ingress,
    List.append_assoc]

private theorem toExec_kept_run {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s0 s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s0.exec)
    (run : JointRun cfg ccfg bls s0 s) :
    (run.toExec pre).kept = pre.kept ++ run.steps.map (fun D => D.stepTrace.trace.kept) := by
  induction run with
  | nil => simp only [JointRun.toExec_nil, JointRun.steps_nil, List.map_nil, List.append_nil]
  | snoc run b step bound ih =>
    simp only [JointRun.toExec_snoc, JointRun.steps_snoc, ConfiguredHistoryTrace.kept,
      List.map_append, List.map_singleton, ih, List.append_assoc]

private theorem toExec_kept_ingress {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec)
    (ingress : JointRunIngress cfg ccfg bls anchor final) :
    (ingress.toExec pre).kept = pre.kept ++ ingress.steps.map (fun D => D.stepTrace.trace.kept) := by
  cases ingress with
  | standard run => exact toExec_kept_run pre run
  | atElectraSlot _ _ _ _ firstStep firstBound tail =>
    simp only [JointRunIngress.toExec, JointRunIngress.steps, toExec_kept_run,
      ConfiguredHistoryTrace.kept, List.map_cons, List.append_assoc, List.singleton_append]

private theorem toExec_sysRaw_run {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s0 s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s0.exec)
    (run : JointRun cfg ccfg bls s0 s) :
    (run.toExec pre).systemRawFrames =
      pre.systemRawFrames ++ run.steps.flatMap (fun D => D.stepTrace.trace.systemRawFrames) := by
  induction run with
  | nil => simp only [JointRun.toExec_nil, JointRun.steps_nil, List.flatMap_nil, List.append_nil]
  | snoc run b step bound ih =>
    simp only [JointRun.toExec_snoc, JointRun.steps_snoc, ConfiguredHistoryTrace.systemRawFrames,
      List.flatMap_append, List.flatMap_singleton, ih, List.append_assoc]

private theorem toExec_sysRaw_ingress {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec)
    (ingress : JointRunIngress cfg ccfg bls anchor final) :
    (ingress.toExec pre).systemRawFrames =
      pre.systemRawFrames ++ ingress.steps.flatMap (fun D => D.stepTrace.trace.systemRawFrames) := by
  cases ingress with
  | standard run => exact toExec_sysRaw_run pre run
  | atElectraSlot _ _ _ _ firstStep firstBound tail =>
    simp only [JointRunIngress.toExec, JointRunIngress.steps, toExec_sysRaw_run,
      ConfiguredHistoryTrace.systemRawFrames, List.flatMap_cons, List.append_assoc]

private theorem filter_depositType_getExecutionRequestsList {P : Preset}
    (reqs : ExecutionRequests P) :
    (getExecutionRequestsList reqs).filter
      (fun e => decide (e.head? = some JauneConsensus.depositRequestType)) =
    if (Ssz.serialize reqs.deposits).isEmpty then []
    else [JauneConsensus.depositRequestType :: Ssz.serialize reqs.deposits] := by
  simp only [getExecutionRequestsList, List.filterMap_cons, List.filterMap_nil]
  cases (Ssz.serialize reqs.deposits).isEmpty <;>
    cases (Ssz.serialize reqs.withdrawals).isEmpty <;>
    cases (Ssz.serialize reqs.consolidations).isEmpty <;> rfl

/-- Joined `D-S8` corollary: each post-cutover joint step's consensus deposit requests serialize to
its kept execution deposit records, in order. -/
theorem d8_joined : D8Joined := by
  intro P ccfg bls anchor final v j D hD
  let d := fullDeployment v
  have codeP : DepositCodeAt d.P.state := prague_depositCode v
  have hmemD : D ∈ v.ingress.steps := List.mem_of_getElem? hD
  have hmemKept : D.stepTrace.trace.kept ∈ d.modern.kept := by
    change D.stepTrace.trace.kept ∈
      (v.ingress.toExec (concatConfiguredHistory v.deployment.modern v.pre)).kept
    rw [toExec_kept_ingress]
    exact List.mem_append_right _ (List.mem_map_of_mem hmemD)
  obtain ⟨hlen192, houtReq, hnoType0, htxEq⟩ :=
    Blanc.Composition.DepositRequests.d_s8 d.modern.keptHistory d.modern.kept_covered codeP
      D.stepTrace.trace.kept hmemKept
  have avoid := d.modern.systemCreateAvoid d.anchors.pragueInstalled d.modernSystemNoAuthority
  have sysAll := system_of_installed d.modern d.anchors.pragueInstalled
    d.modernSystemNoAuthority avoid.2 codeP
  have sysBlk : ∀ fr ∈ D.stepTrace.trace.bodyTrace.beacon.settledFrames ++
      D.stepTrace.trace.bodyTrace.history.settledFrames ++
      D.stepTrace.trace.bodyTrace.requests.settledFrames,
      fr.sevm.currentTarget ≠ depositAddr := by
    intro fr hfr
    have hraw : Blanc.Exec.Frame.rootDeriv (frame := fr) ∈ D.stepTrace.trace.systemRawFrames := by
      simp only [ConfiguredBlockTrace.systemRawFrames, AppliedBodyTrace.systemRawFrames,
        RequestsTrace.settledFrames, RequestsTrace.rawFrames, List.mem_append] at hfr ⊢
      rcases hfr with (hb | hh) | hw | hc
      · exact Or.inl (Or.inl (D.stepTrace.trace.bodyTrace.beacon.mem_rawFrames_of_mem_settledFrames fr hb))
      · exact Or.inl (Or.inr (D.stepTrace.trace.bodyTrace.history.mem_rawFrames_of_mem_settledFrames fr hh))
      · exact Or.inr (Or.inl (D.stepTrace.trace.bodyTrace.requests.withdrawal.mem_rawFrames_of_mem_settledFrames fr hw))
      · exact Or.inr (Or.inr (D.stepTrace.trace.bodyTrace.requests.consolidation.mem_rawFrames_of_mem_settledFrames fr hc))
    have hinMod : Blanc.Exec.Frame.rootDeriv (frame := fr) ∈ d.modern.systemRawFrames := by
      change _ ∈ (v.ingress.toExec (concatConfiguredHistory v.deployment.modern v.pre)).systemRawFrames
      rw [toExec_sysRaw_ingress]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨D, hmemD, hraw⟩)
    exact sysAll _ hinMod
  have hkeptEq := htxEq (ConfiguredBlockTrace.kept_systemRoots_keptAt_nil D.stepTrace.trace depositAddr sysBlk)
  rw [hkeptEq]
  obtain ⟨reqs, hread, hreqList⟩ := ofBlock_executionRequests D.stepTrace.ofBlock
  have hstepReqs : stepDepositRequests D = reqs.deposits.toArray.toList := by
    simp only [stepDepositRequests, hread]
  have hserDep : Ssz.serialize reqs.deposits =
      (stepDepositRequests D).flatMap Ssz.serialize := by
    rw [hstepReqs, serialize_sszList_of_fixedSize (k := 192) rfl]
  have hboth : D.stepTrace.trace.kept.output.requests = getExecutionRequestsList reqs :=
    D.stepTrace.requests_eq.trans hreqList
  rw [houtReq] at hboth
  let isDepEntry : Bytes → Bool := fun e => decide (e.head? = some JauneConsensus.depositRequestType)
  have hfilt := congrArg (List.filter isDepEntry) hboth
  have hrestNil : (D.stepTrace.trace.kept.run.requests.flatMap RequestStep.bytes).filter isDepEntry = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp only [isDepEntry, decide_eq_true_eq]
    exact hnoType0 e he
  simp only [List.filter_append, hrestNil, List.append_nil] at hfilt
  rw [show isDepEntry = (fun e => decide (e.head? = some JauneConsensus.depositRequestType)) from rfl,
    filter_depositType_getExecutionRequestsList, hserDep] at hfilt
  set lhs := ((D.stepTrace.trace.kept.run.txRoots.flatMap (Root.keptAt depositAddr)).flatMap frameRecords).flatten
  set rhs := (stepDepositRequests D).flatMap Ssz.serialize
  have hflatEq : rhs = lhs := by
    cases hl : lhs <;> cases hr : rhs
    · rfl
    · rw [hl, hr] at hfilt; cases hfilt
    · rw [hl, hr] at hfilt; cases hfilt
    · rw [hl, hr] at hfilt
      exact List.cons.inj (List.head_eq_of_cons_eq hfilt).symm |>.2
  have hc := congrArg (Blanc.List.chunksOf 192) hflatEq
  dsimp only [lhs, rhs] at hc
  rw [Blanc.List.chunksOf_flatMap (by decide : 0 < 192) Ssz.serialize (stepDepositRequests D)
      (fun dr _ => serialize_depositRequest_length dr),
    ← List.flatMap_id,
    Blanc.List.chunksOf_flatMap (by decide : 0 < 192) id _ hlen192,
    List.map_id] at hc
  exact hc

private abbrev atDepositAddr (fr : Exec.Frame) : Bool :=
  decide (fr.sevm.currentTarget = depositAddr)

private abbrev isDepositFrame (fr : Exec.Frame) : Bool :=
  decide (fr.sevm.currentTarget = depositAddr ∧ Sevm.selector fr.sevm = BeaconDeposit.depositSelector)

private def expectedRecord (fr : Exec.Frame) (idx : Nat) : Bytes :=
  depositRecord ⟨argBytes fr.sevm 0, argBytes fr.sevm 1,
    BeaconDeposit.le64 (fr.sevm.value.toNat / BeaconDeposit.oneGwei),
    argBytes fr.sevm 2, BeaconDeposit.le64 idx⟩

private theorem flatMap_committedFrameNodes_eq (fs : List Exec.Frame) :
    fs.flatMap (committedFrameNodes depositAddr) =
      (fs.filter isDepositFrame).map (fun fr => frameNode fr.sevm) := by
  induction fs with
  | nil => rfl
  | cons fr rest ih =>
    simp only [List.flatMap_cons, List.filter_cons, committedFrameNodes, frameAccepted,
      isDepositFrame, ih]
    by_cases ht : fr.sevm.currentTarget = depositAddr
    · by_cases hs : Sevm.selector fr.sevm = BeaconDeposit.depositSelector
      · simp only [ht, hs, and_self, decide_true, ↓reduceIte, List.map_cons, List.singleton_append]
      · simp only [ht, hs, and_false, decide_false, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    · simp only [ht, false_and, decide_false, Bool.false_eq_true, ↓reduceIte, List.nil_append]

private theorem length_committedFrameNodes (fs : List Exec.Frame) :
    (fs.flatMap (committedFrameNodes depositAddr)).length = (fs.filter isDepositFrame).length := by
  rw [flatMap_committedFrameNodes_eq, List.length_map]

private theorem frameRecords_nil_of_logs_nil {fr : Exec.Frame} (h : frameLogs fr = []) :
    frameRecords fr = [] := by
  simp only [frameRecords, depositLogs, h, List.filter_nil, List.filterMap_nil]

private theorem supportsInterfaceSelector_val :
    BeaconDeposit.supportsInterfaceSelector = 0x01ffc9a7 := by
  decide +kernel

private theorem single_frame_dichotomy {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final)
    (idx : Nat) (fr : Exec.Frame)
    (hlookup : v.fullTrace.settledFrames[idx]? = some fr)
    (htarget : fr.sevm.currentTarget = depositAddr) :
    let k := ((v.fullTrace.settledFrames.take idx).filter isDepositFrame).length
    (Sevm.selector fr.sevm = BeaconDeposit.depositSelector ∧
      frameRecords fr = [expectedRecord fr k] ∧
      (argBytes fr.sevm 0).length = 48 ∧ (argBytes fr.sevm 1).length = 32 ∧
      (argBytes fr.sevm 2).length = 96 ∧
      fr.sevm.value.toNat / BeaconDeposit.oneGwei < 2 ^ 64 ∧
      k < 2 ^ 32 - 1 ∧
      (fr.sevm.value.toNat / BeaconDeposit.oneGwei) * 10 ^ 9 = fr.sevm.value.toNat) ∨
    (Sevm.selector fr.sevm ≠ BeaconDeposit.depositSelector ∧ frameRecords fr = []) := by
  have hlookup2 : (fullDeployment v).trace.settledFrames[idx]? = some fr := hlookup
  obtain ⟨hinv, o, hcls, _⟩ := Blanc.Composition.DepositClassified.d_s2 (fullDeployment v) idx fr hlookup2 htarget
  have hlen : ((fullDeployment v).trace.settledFrames.take idx |>.flatMap (committedFrameNodes depositAddr)).length =
      ((v.fullTrace.settledFrames.take idx).filter isDepositFrame).length :=
    length_committedFrameNodes _
  cases o with
  | deposit =>
    obtain ⟨hrec, hpk, hwc, hsig, hamt, hk, hmul⟩ := frame_record fr _ hinv hcls
    rw [hlen] at hrec hk
    exact Or.inl ⟨hcls.1, hrec, hpk, hwc, hsig, hamt, hk, hmul⟩
  | getDepositRoot =>
    have hsel : Sevm.selector fr.sevm ≠ BeaconDeposit.depositSelector := by
      rw [hcls.1, BeaconDeposit.getDepositRootSelector_eq, BeaconDeposit.depositSelector_eq]; decide
    exact Or.inr ⟨hsel, frameRecords_nil_of_logs_nil hcls.2.2.2.2.1⟩
  | getDepositCount =>
    have hsel : Sevm.selector fr.sevm ≠ BeaconDeposit.depositSelector := by
      rw [hcls.1, BeaconDeposit.getDepositCountSelector_eq, BeaconDeposit.depositSelector_eq]; decide
    exact Or.inr ⟨hsel, frameRecords_nil_of_logs_nil hcls.2.2.2.2.1⟩
  | supportsInterface =>
    have hsel : Sevm.selector fr.sevm ≠ BeaconDeposit.depositSelector := by
      rw [hcls.1, supportsInterfaceSelector_val, BeaconDeposit.depositSelector_eq]; decide
    exact Or.inr ⟨hsel, frameRecords_nil_of_logs_nil hcls.2.2.2.2.2.1⟩

private theorem slice_records {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final)
    (fs after : List Exec.Frame) :
    ∀ (before : List Exec.Frame),
      v.fullTrace.settledFrames = before ++ fs ++ after →
      let recs := (fs.filter atDepositAddr).flatMap frameRecords
      let deps := fs.filter isDepositFrame
      let k0 := (before.filter isDepositFrame).length
      recs.length = deps.length ∧
      ∀ (rIdx : Nat) (fr : Exec.Frame), deps[rIdx]? = some fr →
        recs[rIdx]? = some (expectedRecord fr (k0 + rIdx)) ∧
        (argBytes fr.sevm 0).length = 48 ∧ (argBytes fr.sevm 1).length = 32 ∧
        (argBytes fr.sevm 2).length = 96 ∧
        fr.sevm.value.toNat / BeaconDeposit.oneGwei < 2 ^ 64 ∧
        k0 + rIdx < 2 ^ 64 ∧
        (fr.sevm.value.toNat / BeaconDeposit.oneGwei) * 10 ^ 9 = fr.sevm.value.toNat := by
  induction fs with
  | nil =>
    intro before _
    simp only [List.filter_nil, List.flatMap_nil, List.length_nil, List.getElem?_nil,
      reduceCtorEq, false_implies, implies_true, and_self]
  | cons fr rest ih =>
    intro before hslice
    have hsliceNext : v.fullTrace.settledFrames = (before ++ [fr]) ++ rest ++ after := by
      simpa only [List.append_assoc, List.singleton_append] using hslice
    have hlookup : v.fullTrace.settledFrames[before.length]? = some fr := by
      rw [hslice, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.cons_append, List.getElem?_cons_zero]
    have htake : v.fullTrace.settledFrames.take before.length = before := by
      rw [hslice, List.append_assoc, List.take_left]
    by_cases ht : fr.sevm.currentTarget = depositAddr
    · rcases single_frame_dichotomy v before.length fr hlookup ht with
        ⟨hsel, hrec, hpk, hwc, hsig, hamt, hk, hmul⟩ | ⟨hsel, hrec⟩
      · rw [htake] at hrec hk
        have hat : atDepositAddr fr = true := decide_eq_true ht
        have his : isDepositFrame fr = true := decide_eq_true ⟨ht, hsel⟩
        obtain ⟨hlenRest, hidxRest⟩ := ih (before ++ [fr]) hsliceNext
        have hkNext : ((before ++ [fr]).filter isDepositFrame).length =
            (before.filter isDepositFrame).length + 1 := by
          simp only [List.filter_append, List.filter_cons, List.filter_nil, his, ↓reduceIte,
            List.length_append, List.length_singleton]
        rw [hkNext] at hidxRest
        dsimp only
        simp only [List.filter_cons, hat, his, ↓reduceIte, List.flatMap_cons, hrec,
          List.singleton_append, List.length_cons, hlenRest, true_and]
        intro rIdx fr2 hfr2
        cases rIdx with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hfr2
          subst hfr2
          simp only [List.getElem?_cons_zero, Nat.add_zero, true_and]
          exact ⟨hpk, hwc, hsig, hamt, by omega, hmul⟩
        | succ rIdx2 =>
          simp only [List.getElem?_cons_succ] at hfr2 ⊢
          simpa only [Nat.add_right_comm, Nat.add_assoc] using hidxRest rIdx2 fr2 hfr2
      · have hat : atDepositAddr fr = true := decide_eq_true ht
        have his : isDepositFrame fr = false := decide_eq_false (fun h => hsel h.2)
        obtain ⟨hlenRest, hidxRest⟩ := ih (before ++ [fr]) hsliceNext
        have hkNext : ((before ++ [fr]).filter isDepositFrame).length =
            (before.filter isDepositFrame).length := by
          simp only [List.filter_append, List.filter_cons, List.filter_nil, his,
            Bool.false_eq_true, ↓reduceIte, List.append_nil]
        rw [hkNext] at hidxRest
        dsimp only
        simp only [List.filter_cons, hat, his, Bool.false_eq_true, ↓reduceIte,
          List.flatMap_cons, hrec, List.nil_append]
        exact ⟨hlenRest, hidxRest⟩
    · have hat : atDepositAddr fr = false := decide_eq_false ht
      have his : isDepositFrame fr = false := decide_eq_false (fun h => ht h.1)
      obtain ⟨hlenRest, hidxRest⟩ := ih (before ++ [fr]) hsliceNext
      have hkNext : ((before ++ [fr]).filter isDepositFrame).length =
          (before.filter isDepositFrame).length := by
        simp only [List.filter_append, List.filter_cons, List.filter_nil, his,
          Bool.false_eq_true, ↓reduceIte, List.append_nil]
      rw [hkNext] at hidxRest
      dsimp only
      simp only [List.filter_cons, hat, his, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlenRest, hidxRest⟩

private theorem step_keptAt_eq_filter {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final)
    {D : JointRunStep (P := P) mainnetChainConfig ccfg bls}
    (hmemD : D ∈ v.ingress.steps) :
    D.stepTrace.trace.kept.keptAt depositAddr =
      D.stepTrace.trace.settledFrames.filter atDepositAddr := by
  refine ConfiguredBlockTrace.keptAt_eq_filter_settledFrames_of_leaves D.stepTrace.trace depositAddr ?_
  intro fr hfr htarget
  refine fullTrace_leaves v fr ?_ htarget
  rw [fullTrace_settledFrames]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨D, hmemD, hfr⟩)

private theorem ingress_serialize_eq {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    (ingressDepositRequests v.ingress).map Ssz.serialize =
      ((v.ingress.steps.flatMap (fun D => D.stepTrace.trace.settledFrames)).filter
        atDepositAddr).flatMap frameRecords := by
  unfold ingressDepositRequests
  rw [List.map_flatMap, List.filter_flatMap, List.flatMap_assoc]
  refine List.flatMap_congr fun D hmemD => ?_
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemD
  rw [d8_joined v j D hj, step_keptAt_eq_filter v hmemD]

/-- `D-S9` delivery endpoint: step-by-step exact request records, contiguous index range from
`E₀`, and final committed deposit count `E_final`. -/
theorem d9_delivery : D9Delivery := by
  intro P ccfg bls anchor final v
  refine ⟨fun j D hj => d8_joined v j D hj, ?_, ?_⟩
  · set allFs := v.ingress.steps.flatMap (fun D => D.stepTrace.trace.settledFrames)
    have hslice : v.fullTrace.settledFrames = v.anchorTrace.settledFrames ++ allFs ++ [] := by
      rw [List.append_nil, fullTrace_settledFrames]
    obtain ⟨hlen, hidx⟩ := slice_records v allFs [] v.anchorTrace.settledFrames hslice
    have hser := ingress_serialize_eq v
    have hreqLen : (ingressDepositRequests v.ingress).length = (allFs.filter isDepositFrame).length := by
      have := congrArg List.length hser
      rw [List.length_map] at this
      exact this.trans hlen
    have hk0 : (v.anchorTrace.settledFrames.filter isDepositFrame).length = v.E₀ := by
      simp only [DepositJoint.E₀, committedNodesIn]
      exact (length_committedFrameNodes _).symm
    refine List.ext_getElem (by simp only [List.length_map, List.length_range']) ?_
    intro i hi1 hi2
    rw [List.length_map] at hi1
    have hiDep : i < (allFs.filter isDepositFrame).length := hreqLen ▸ hi1
    have hdepSome : (allFs.filter isDepositFrame)[i]? = some ((allFs.filter isDepositFrame)[i]'hiDep) :=
      List.getElem?_eq_getElem hiDep
    obtain ⟨hrecAt, hpk, hwc, hsig, hamt, hkBound, _⟩ := hidx i _ hdepSome
    have hserAt : ((ingressDepositRequests v.ingress).map Ssz.serialize)[i]? =
        some (Ssz.serialize ((ingressDepositRequests v.ingress)[i]'hi1)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi1, Option.map_some]
    rw [← hser, hserAt, Option.some.injEq] at hrecAt
    rw [hk0] at hrecAt hkBound
    obtain ⟨_, _, _, _, hidxEq⟩ := fields_of_record hpk hwc hsig hamt hkBound hrecAt
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, hidxEq]
  · set allFs := v.ingress.steps.flatMap (fun D => D.stepTrace.trace.settledFrames)
    have hslice : v.fullTrace.settledFrames = v.anchorTrace.settledFrames ++ allFs ++ [] := by
      rw [List.append_nil, fullTrace_settledFrames]
    obtain ⟨hlen, _⟩ := slice_records v allFs [] v.anchorTrace.settledFrames hslice
    have hser := ingress_serialize_eq v
    have hreqLen : (ingressDepositRequests v.ingress).length = (allFs.filter isDepositFrame).length := by
      have := congrArg List.length hser
      rw [List.length_map] at this
      exact this.trans hlen
    have hadr : Creation.depositAddress = depositAddr := rfl
    simp only [DepositJoint.E_final, DepositJoint.E₀, committedNodesIn, hadr,
      length_committedFrameNodes, fullTrace_settledFrames, List.filter_append,
      List.length_append, hreqLen]
    rfl

private theorem fresh_of_anchorLedgerD {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final)
    {tq0 : TQueue} {preApplied : List PreAnchorApplied}
    (hAnchor : AnchorLedgerD v tq0 preApplied) :
    RunIndicesFreshIngress v.ingress tq0 := by
  unfold RunIndicesFreshIngress
  rw [(d9_delivery v).2.1]
  refine List.nodup_append.mpr ⟨hAnchor.1.2.2, List.nodup_range', ?_⟩
  intro x hx1 y hy hxy
  subst hxy
  obtain ⟨e, he, hfst⟩ := List.mem_filterMap.mp hx1
  rcases e with ⟨tag, pd⟩
  cases tag with
  | none => cases hfst
  | some n =>
    simp only [Option.some.injEq] at hfst
    subst hfst
    have hn := (hAnchor.2.2.2.1 n pd he).2.1
    have hm := (List.mem_range'_1.mp hy).1
    omega

/-- Joined `D-S9` Wei/Gwei conservation endpoint across post-cutover joint ingress. -/
theorem d9_conservation_joined : D9ConservationJoined := by
  intro P ccfg anchor final v tq0 preApplied hAnchor
  dsimp only
  obtain ⟨tqF, ap, hrun, hcons⟩ := Blanc.Composition.DepositLedgerFate.depositConservation
    v.ingress tq0 v.stepsPostGenesis hAnchor.1 (fresh_of_anchorLedgerD v hAnchor)
  set allFs := v.ingress.steps.flatMap (fun D => D.stepTrace.trace.settledFrames)
  have hkeptFlat : v.ingress.steps.flatMap (fun D => D.stepTrace.trace.kept.keptAt depositAddr) =
      allFs.filter atDepositAddr := by
    rw [List.filter_flatMap]
    exact List.flatMap_congr fun D hmemD => step_keptAt_eq_filter v hmemD
  have hfiltEq : (allFs.filter atDepositAddr).filter
      (fun fr => decide (Sevm.selector fr.sevm = BeaconDeposit.depositSelector)) =
      allFs.filter isDepositFrame := by
    rw [List.filter_filter]
    refine List.filter_congr fun fr _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_comm]
  have hslice : v.fullTrace.settledFrames = v.anchorTrace.settledFrames ++ allFs ++ [] := by
    rw [List.append_nil, fullTrace_settledFrames]
  obtain ⟨hlen, hidx⟩ := slice_records v allFs [] v.anchorTrace.settledFrames hslice
  have hser := ingress_serialize_eq v
  have hreqLen : (ingressDepositRequests v.ingress).length = (allFs.filter isDepositFrame).length := by
    have := congrArg List.length hser
    rw [List.length_map] at this
    exact this.trans hlen
  have hk0 : (v.anchorTrace.settledFrames.filter isDepositFrame).length = v.E₀ := by
    simp only [DepositJoint.E₀, committedNodesIn]
    exact (length_committedFrameNodes _).symm
  have hweiList : (ingressDepositRequests v.ingress).map (fun dr => dr.amount.toNat * 10 ^ 9) =
      (allFs.filter isDepositFrame).map (fun fr => fr.sevm.value.toNat) := by
    refine List.ext_getElem (by simp only [List.length_map, hreqLen]) ?_
    intro i hi1 hi2
    rw [List.length_map] at hi1 hi2
    have hdepSome : (allFs.filter isDepositFrame)[i]? = some ((allFs.filter isDepositFrame)[i]'hi2) :=
      List.getElem?_eq_getElem hi2
    obtain ⟨hrecAt, hpk, hwc, hsig, hamt, hkBound, hmul⟩ := hidx i _ hdepSome
    have hserAt : ((ingressDepositRequests v.ingress).map Ssz.serialize)[i]? =
        some (Ssz.serialize ((ingressDepositRequests v.ingress)[i]'hi1)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi1, Option.map_some]
    rw [← hser, hserAt, Option.some.injEq] at hrecAt
    rw [hk0] at hrecAt hkBound
    obtain ⟨_, _, _, hamtEq, _⟩ := fields_of_record hpk hwc hsig hamt hkBound hrecAt
    simp only [List.getElem_map, hamtEq, hmul]
  have hsumMul : ∀ ns : List Nat, ns.sum * 10 ^ 9 = (ns.map (fun n => n * 10 ^ 9)).sum := by
    intro ns
    induction ns with
    | nil => simp only [List.sum_nil, Nat.zero_mul, List.map_nil]
    | cons n ns ih => simp only [List.sum_cons, List.map_cons, Nat.add_mul, ih]
  have hweiEq : ((ingressDepositRequests v.ingress).map (fun dr => dr.amount.toNat)).sum * 10 ^ 9 =
      ((v.ingress.steps.flatMap fun D => D.stepTrace.trace.kept.keptAt depositAddr).filter
        (fun fr => decide (Sevm.selector fr.sevm = BeaconDeposit.depositSelector))).foldr
        (fun fr acc => fr.sevm.value.toNat + acc) 0 := by
    rw [hkeptFlat, hfiltEq, ← List.foldr_map, ← List.sum_eq_foldr, hsumMul,
      List.map_map, Function.comp_def, hweiList]
  have htotEq : (creditedTotal (jointCtx ccfg true) ap +
      uncreditedTotal (jointCtx ccfg true) ap + taggedTotal tqF) * 10 ^ 9 =
      taggedTotal tq0 * 10 ^ 9 +
        ((v.ingress.steps.flatMap fun D => D.stepTrace.trace.kept.keptAt depositAddr).filter
          (fun fr => decide (Sevm.selector fr.sevm = BeaconDeposit.depositSelector))).foldr
          (fun fr acc => fr.sevm.value.toNat + acc) 0 := by
    rw [hcons, Nat.add_mul, hweiEq]
  refine ⟨tqF, ap, hrun, htotEq, ?_⟩
  rw [← htotEq]
  exact Nat.mul_le_mul_right (10 ^ 9) (by omega)

private theorem committedDepositDataIn_length {cfg : ChainConfig} {D B : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg D B) :
    (committedDepositDataIn trace).length = (committedNodesIn Creation.depositAddress trace).length := by
  have hadr : Creation.depositAddress = depositAddr := rfl
  simp only [committedDepositDataIn, committedNodesIn, hadr, List.length_map,
    length_committedFrameNodes]

private theorem anchor_deposits_append {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    committedDepositDataIn v.anchorTrace =
      committedDepositDataIn v.deployment.trace ++
        (v.pre.settledFrames.filter isDepositFrame).map frameDepositData := by
  simp only [committedDepositDataIn, anchorTrace_settledFrames, List.filter_append, List.map_append]

private theorem full_deposits_append {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final) :
    committedDepositDataIn v.fullTrace =
      committedDepositDataIn v.anchorTrace ++
        ((v.ingress.steps.flatMap (fun D => D.stepTrace.trace.settledFrames)).filter
          isDepositFrame).map frameDepositData := by
  simp only [committedDepositDataIn, fullTrace_settledFrames, List.filter_append, List.map_append]

private theorem step_request_correspondence {P : Preset} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (v : DepositJoint ccfg bls anchor final)
    (j : Nat) (D : JointRunStep (P := P) mainnetChainConfig ccfg bls)
    (hD : v.ingress.steps[j]? = some D)
    (rIdx : Nat) (dr : DepositRequest) (hdr : (stepDepositRequests D)[rIdx]? = some dr) :
    v.E₀ ≤ dr.index.toNat ∧ dr.index.toNat < v.E_final ∧
    ∃ fr ∈ D.stepTrace.trace.kept.keptAt depositAddr,
      Sevm.selector fr.sevm = BeaconDeposit.depositSelector ∧
      dr.amount.toNat * 10 ^ 9 = fr.sevm.value.toNat ∧
      dr.pubkey.toArray.toList = argBytes fr.sevm 0 ∧
      dr.withdrawal_credentials.toBytes = argBytes fr.sevm 1 ∧
      dr.signature.toArray.toList = argBytes fr.sevm 2 ∧
      (committedDepositDataIn v.fullTrace)[dr.index.toNat]? = some (frameDepositData fr) := by
  set before := v.anchorTrace.settledFrames ++
    (v.ingress.steps.take j).flatMap (fun E => E.stepTrace.trace.settledFrames)
  set fs := D.stepTrace.trace.settledFrames
  set after := (v.ingress.steps.drop (j + 1)).flatMap (fun E => E.stepTrace.trace.settledFrames)
  have hsplit := congrArg (List.flatMap (fun E : JointRunStep (P := P) mainnetChainConfig ccfg bls =>
    E.stepTrace.trace.settledFrames)) (Blanc.List.eq_take_cons_drop hD)
  simp only [List.flatMap_append, List.flatMap_cons] at hsplit
  have hslice : v.fullTrace.settledFrames = before ++ fs ++ after := by
    rw [fullTrace_settledFrames, hsplit]
    simp only [before, fs, after, List.append_assoc]
  obtain ⟨hlen, hidx⟩ := slice_records v fs after before hslice
  have hser := d8_joined v j D hD
  rw [step_keptAt_eq_filter v (List.mem_of_getElem? hD)] at hser
  have hrBound : rIdx < (stepDepositRequests D).length := (List.getElem?_eq_some_iff.mp hdr).1
  have hdepLen : (stepDepositRequests D).length = (fs.filter isDepositFrame).length := by
    have := congrArg List.length hser
    rw [List.length_map] at this
    exact this.trans hlen
  have hrDep : rIdx < (fs.filter isDepositFrame).length := hdepLen ▸ hrBound
  set fr := (fs.filter isDepositFrame)[rIdx]'hrDep
  have hfrSome : (fs.filter isDepositFrame)[rIdx]? = some fr := List.getElem?_eq_getElem hrDep
  obtain ⟨hrecAt, hpk, hwc, hsig, hamt, hkBound, hmul⟩ := hidx rIdx fr hfrSome
  have hserAt : ((stepDepositRequests D).map Ssz.serialize)[rIdx]? = some (Ssz.serialize dr) := by
    rw [List.getElem?_map, hdr, Option.map_some]
  rw [← hser, hserAt, Option.some.injEq] at hrecAt
  obtain ⟨hpkEq, hwcEq, hsigEq, hamtEq, hidxEq⟩ := fields_of_record hpk hwc hsig hamt hkBound hrecAt
  have hk0Lo : v.E₀ ≤ (before.filter isDepositFrame).length := by
    have hadr : Creation.depositAddress = depositAddr := rfl
    simp only [DepositJoint.E₀, committedNodesIn, hadr, length_committedFrameNodes,
      before, List.filter_append, List.length_append]
    omega
  have hkHi : (before.filter isDepositFrame).length + rIdx < v.E_final := by
    have hadr : Creation.depositAddress = depositAddr := rfl
    have htot : v.E_final = (v.fullTrace.settledFrames.filter isDepositFrame).length := by
      simp only [DepositJoint.E_final, committedNodesIn, hadr, length_committedFrameNodes]
    rw [htot, hslice]
    simp only [List.filter_append, List.length_append]
    omega
  have hfrMem : fr ∈ fs.filter isDepositFrame := List.getElem_mem hrDep
  obtain ⟨hfrInFs, hfrPred⟩ := List.mem_filter.mp hfrMem
  simp only [decide_eq_true_eq] at hfrPred
  have hfrKept : fr ∈ D.stepTrace.trace.kept.keptAt depositAddr := by
    rw [step_keptAt_eq_filter v (List.mem_of_getElem? hD)]
    exact List.mem_filter.mpr ⟨hfrInFs, decide_eq_true hfrPred.1⟩
  have hfullLookup : (committedDepositDataIn v.fullTrace)[dr.index.toNat]? = some (frameDepositData fr) := by
    unfold committedDepositDataIn
    change ((v.fullTrace.settledFrames.filter isDepositFrame).map frameDepositData)[dr.index.toNat]? = _
    rw [List.getElem?_map, hslice, hidxEq]
    simp only [List.filter_append]
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_append_left hrDep, hfrSome, Option.map_some]
  exact ⟨by omega, by omega, fr, hfrKept, hfrPred.2, by rw [hamtEq, hmul], hpkEq, hwcEq, hsigEq, hfullLookup⟩

/-- Joined `D-S9` exclusive fate endpoint across `[cutoverCount, E_final)` over deployment-rooted
joint Electra/Fulu execution. -/
theorem d9_fate_joined : D9FateJoined := by
  intro P ccfg anchor final v tq0 preApplied hAnchor
  dsimp only
  have hfresh := fresh_of_anchorLedgerD v hAnchor
  have hEfinalEq := (d9_delivery v).2.2
  have hcutLe : v.cutoverCount ≤ v.E₀ := by
    have h := congrArg List.length (anchor_deposits_append v)
    rw [List.length_append, committedDepositDataIn_length, committedDepositDataIn_length] at h
    unfold DepositJoint.cutoverCount DepositJoint.E₀ BeaconDeploymentTo.deposits
    omega
  have hE0Le : v.E₀ ≤ v.E_final := by omega
  have hdepLen : (committedDepositDataIn v.fullTrace).length = v.E_final :=
    committedDepositDataIn_length v.fullTrace
  have hdepTake : (committedDepositDataIn v.fullTrace).take v.cutoverCount =
      committedDepositDataIn v.deployment.trace := by
    rw [full_deposits_append, anchor_deposits_append, List.append_assoc]
    have hlen : (committedDepositDataIn v.deployment.trace).length = v.cutoverCount :=
      committedDepositDataIn_length v.deployment.trace
    rw [← hlen, List.take_left]
  have hlegacy : ∀ k < v.cutoverCount,
      (∀ rec ∈ preApplied, rec.index ≠ k) ∧
      (∀ e ∈ tq0, e.1 ≠ some k) ∧
      (∀ dr ∈ ingressDepositRequests v.ingress, dr.index.toNat ≠ k) := by
    intro k hk
    refine ⟨?_, ?_, ?_⟩
    · intro rec hrec
      have := (hAnchor.2.2.1 rec hrec).1
      omega
    · intro e he htag
      rcases e with ⟨t, pd⟩
      dsimp only at htag
      subst htag
      have := (hAnchor.2.2.2.1 k pd he).1
      omega
    · intro dr hdr
      have hmem : dr.index.toNat ∈ (ingressDepositRequests v.ingress).map (fun r => r.index.toNat) :=
        List.mem_map_of_mem hdr
      rw [(d9_delivery v).2.1] at hmem
      have := (List.mem_range'_1.mp hmem).1
      omega
  obtain ⟨linked, valid⟩ := ingressFacts v.ingress v.stepsPostGenesis
  have sourceFresh : ((tagged tq0 ++ v.ingress.steps.flatMap requestEntries).map Prod.fst).Nodup := by
    rw [sourceTags]
    exact List.Nodup.map (Option.some_injective Nat) hfresh
  obtain ⟨tqF, ap, run, alignedF, moved, uniqueTags, calls, chrono, _⟩ :=
    ledgerRun v.ingress.steps 0 anchor final tq0 [] linked valid hAnchor.1.1 sourceFresh
  refine ⟨hfresh, hcutLe, hE0Le, hEfinalEq, hdepLen, hdepTake, hlegacy,
    fun j D hD rIdx dr hdr => step_request_correspondence v j D hD rIdx dr hdr,
    tqF, ap, run, alignedF, ?_⟩
  let all := appliedEntries ap ++ tqF
  have pairwise : all.Pairwise (fun a b => a.1.isSome → b.1.isSome → a.1 ≠ b.1) := by
    change List.Pairwise (fun a b : Tag => a ≠ b) ((tagged all).map Prod.fst) at uniqueTags
    rw [List.pairwise_map, tagged, List.pairwise_filter] at uniqueTags
    exact uniqueTags
  have unique : ∀ {k : Nat} {p p2 : Nat} {e e2 : Tag × PendingDeposit},
      all[p]? = some e → all[p2]? = some e2 →
      e.1 = some k → e2.1 = some k → p = p2 := by
    intro k p p2 e e2 he he2 ht ht2
    obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hp2, rfl⟩ := List.getElem?_eq_some_iff.mp he2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact (List.pairwise_iff_getElem.mp pairwise p p2 hp hp2 hlt
        (by rw [ht]; rfl) (by rw [ht2]; rfl)) (ht.trans ht2.symm)
    · exact (List.pairwise_iff_getElem.mp pairwise p2 p hp2 hp hgt
        (by rw [ht2]; rfl) (by rw [ht]; rfl)) (ht2.trans ht.symm)
  have atApplied : ∀ {p : Nat} {x : Nat × AppliedAt P}, ap[p]? = some x →
      all[p]? = some (x.2.2.tag, x.2.2.deposit) := by
    intro p x hx
    have hp := (List.getElem?_eq_some_iff.mp hx).1
    rw [List.getElem?_append_left (by simpa only [appliedEntries, List.length_map] using hp)]
    simp only [appliedEntries, List.getElem?_map, hx, Option.map_some]
  have atPending : ∀ {p : Nat} {e : Tag × PendingDeposit}, tqF[p]? = some e →
      all[ap.length + p]? = some e := by
    intro p e he
    rw [List.getElem?_append_right (by simp only [appliedEntries, List.length_map]; omega)]
    simpa only [appliedEntries, List.length_map, Nat.add_sub_cancel_left] using he
  intro k hkLo hkHi
  have hkDep : k < (committedDepositDataIn v.fullTrace).length := hdepLen ▸ hkHi
  rcases hdat : (committedDepositDataIn v.fullTrace)[k]'hkDep with ⟨pkBytes, wcBytes, sigBytes, amtGwei⟩
  have hdatSome : (committedDepositDataIn v.fullTrace)[k]? = some (pkBytes, wcBytes, sigBytes, amtGwei) := by
    rw [List.getElem?_eq_getElem hkDep, hdat]
  refine ⟨pkBytes, wcBytes, sigBytes, amtGwei, hdatSome, ?_⟩
  suffices hEntered :
      (k < v.E₀ ∧
        (∃ idx : Nat, ∃ rec : PreAnchorApplied,
          preApplied[idx]? = some rec ∧ rec.index = k ∧
          ∀ idx2 rec2, preApplied[idx2]? = some rec2 → rec2.index = k → idx2 = idx) ∧
        (∀ a ∈ ap, a.2.2.tag ≠ some k) ∧
        (∀ e ∈ tqF, e.1 ≠ some k)) ∨
      ((∀ rec ∈ preApplied, rec.index ≠ k) ∧
        ∃ d : PendingDeposit,
          (some k, d) ∈ tagged tq0 ++ v.ingress.steps.flatMap requestEntries ∧
          d.pubkey.toArray.toList = pkBytes ∧
          d.withdrawal_credentials.toBytes = wcBytes ∧
          d.signature.toArray.toList = sigBytes ∧
          d.amount.toNat = amtGwei ∧
          d.slot ≠ GENESIS_SLOT) by
    rcases hEntered with hPre | ⟨hnoPre, d, hsrc, hpk, hwc, hsig, hamt, hslot⟩
    · exact Or.inl hPre
    · have hpres : (some k, d) ∈ all := (List.mem_filter.mp (moved.mem_iff.mpr hsrc)).1
      rcases List.mem_append.mp hpres with hapMem | htqMem
      · obtain ⟨⟨stepIdx, a⟩, ha, he⟩ := List.mem_map.mp hapMem
        have ht : a.2.tag = some k := (Prod.mk.inj he).1
        have hd : a.2.deposit = d := (Prod.mk.inj he).2
        obtain ⟨apIdx, hap⟩ := List.mem_iff_getElem?.mp ha
        have hAll := atApplied hap
        obtain ⟨_, hstepBound, post, happlied⟩ := calls (stepIdx, a) ha
        rw [Nat.zero_add] at hstepBound
        obtain ⟨o, houtcome⟩ := Blanc.Composition.DepositConsensusOutcomes.applyOutcome_of_success
          ccfg true a.2.pre post a.2.deposit happlied
        refine Or.inr (Or.inl ⟨hnoPre, ?_, apIdx, stepIdx, a, hap, hstepBound, ht, ?_,
          by rw [hd]; exact hpk, by rw [hd]; exact hwc, by rw [hd]; exact hsig,
          by rw [hd]; exact hamt, by rw [hd]; exact hslot, ?_, o, post, houtcome⟩)
        · intro e heMem htag
          obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp heMem
          have same := unique hAll (atPending hp) ht htag
          have bound := (List.getElem?_eq_some_iff.mp hap).1
          omega
        · intro apIdx2 stepIdx2 a2 hap2 ht2
          exact unique (atApplied hap2) hAll ht2 ht
        · intro emitStep D hD hkMap
          obtain ⟨dr, hdrMem, hdrIdx⟩ := List.mem_map.mp hkMap
          have hc := chrono emitStep D dr hD hdrMem (stepIdx, a) ha (hdrIdx ▸ ht)
          omega
      · obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp htqMem
        have hAll := atPending hp
        refine Or.inr (Or.inr ⟨hnoPre, ?_, p, d, hp, ?_, hpk, hwc, hsig, hamt, hslot⟩)
        · intro x hxMem htag
          obtain ⟨apIdx, hap⟩ := List.mem_iff_getElem?.mp hxMem
          have same := unique (atApplied hap) hAll htag rfl
          have bound := (List.getElem?_eq_some_iff.mp hap).1
          omega
        · intro p2 hp2
          cases he : tqF[p2]? with
          | none => simp only [he, Option.map_none, reduceCtorEq] at hp2
          | some e =>
            have ht2 : e.1 = some k := by simpa only [he, Option.map_some, Option.some.injEq] using hp2
            have same := unique (atPending he) hAll ht2 rfl
            omega
  by_cases hkAnchor : k < v.E₀
  · have hanchLookup : (committedDepositDataIn v.anchorTrace)[k]? =
        some (pkBytes, wcBytes, sigBytes, amtGwei) := by
      have hpre : (committedDepositDataIn v.fullTrace)[k]? = (committedDepositDataIn v.anchorTrace)[k]? := by
        rw [full_deposits_append, List.getElem?_append_left
          (by rw [committedDepositDataIn_length]; exact hkAnchor)]
      exact hpre.symm.trans hdatSome
    rcases hAnchor.2.2.2.2 k hkLo hkAnchor with
      ⟨idx, rec, hrecAt, hrecIdx, hrecUniq, hnotTq0⟩ |
      ⟨hnoPre, p, d, hp, hslot, hmatch, _⟩
    · refine Or.inl ⟨hkAnchor, ⟨idx, rec, hrecAt, hrecIdx, hrecUniq⟩, ?_, ?_⟩
      · intro x hxMem htag
        have hinAll : (x.2.2.tag, x.2.2.deposit) ∈ tagged all := by
          refine List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_map_of_mem hxMem), ?_⟩
          rw [htag]; rfl
        rcases List.mem_append.mp (moved.mem_iff.mp hinAll) with hinTq0 | hinReq
        · obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hinTq0).1
          exact hnotTq0 q (by simp only [hq, Option.map_some, htag])
        · obtain ⟨D, hDmem, hdrEntry⟩ := List.mem_flatMap.mp hinReq
          obtain ⟨dr, hdrMem, hdrEq⟩ := List.mem_map.mp hdrEntry
          have hkEq : some dr.index.toNat = some k := (Prod.mk.inj hdrEq).1.trans htag
          have hdrIn : dr.index.toNat ∈ (ingressDepositRequests v.ingress).map (fun r => r.index.toNat) :=
            List.mem_map_of_mem (List.mem_flatMap.mpr ⟨D, hDmem, hdrMem⟩)
          rw [(d9_delivery v).2.1, Option.some.inj hkEq] at hdrIn
          have := (List.mem_range'_1.mp hdrIn).1
          omega
      · intro e heMem htag
        have hinAll : e ∈ tagged all := by
          refine List.mem_filter.mpr ⟨List.mem_append_right _ heMem, ?_⟩
          rw [htag]; rfl
        rcases List.mem_append.mp (moved.mem_iff.mp hinAll) with hinTq0 | hinReq
        · obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hinTq0).1
          exact hnotTq0 q (by simp only [hq, Option.map_some, htag])
        · obtain ⟨D, hDmem, hdrEntry⟩ := List.mem_flatMap.mp hinReq
          obtain ⟨dr, hdrMem, hdrEq⟩ := List.mem_map.mp hdrEntry
          have hkEq : some dr.index.toNat = some k := (Prod.mk.inj hdrEq).1.trans htag
          have hdrIn : dr.index.toNat ∈ (ingressDepositRequests v.ingress).map (fun r => r.index.toNat) :=
            List.mem_map_of_mem (List.mem_flatMap.mpr ⟨D, hDmem, hdrMem⟩)
          rw [(d9_delivery v).2.1, Option.some.inj hkEq] at hdrIn
          have := (List.mem_range'_1.mp hdrIn).1
          omega
    · have hinj := Option.some.inj (hmatch.symm.trans hanchLookup)
      simp only [Prod.mk.injEq] at hinj
      obtain ⟨hpk, hwc, hsig, hamt⟩ := hinj
      have hinTq0 : (some k, d) ∈ tagged tq0 :=
        List.mem_filter.mpr ⟨List.mem_of_getElem? hp, rfl⟩
      exact Or.inr ⟨hnoPre, d, List.mem_append_left _ hinTq0, hpk, hwc, hsig, hamt, hslot⟩
  · have hnoPre : ∀ rec ∈ preApplied, rec.index ≠ k := by
      intro rec hrec
      have := (hAnchor.2.2.1 rec hrec).2
      omega
    let q := k - v.E₀
    have hq : q < (ingressDepositRequests v.ingress).length := by omega
    let dr := (ingressDepositRequests v.ingress)[q]'hq
    have hdrIdx : dr.index.toNat = k := by
      have hmapEq := congrArg (fun xs => xs[q]?) (d9_delivery v).2.1
      have hqRange : q < (List.range' v.E₀ (ingressDepositRequests v.ingress).length).length := by
        rw [List.length_range']; exact hq
      rw [List.getElem?_map, List.getElem?_eq_getElem hq, Option.map_some,
        List.getElem?_eq_getElem hqRange, List.getElem_range', Nat.one_mul, Option.some.injEq] at hmapEq
      change dr.index.toNat = v.E₀ + q at hmapEq
      omega
    have hdrMem : dr ∈ v.ingress.steps.flatMap stepDepositRequests := List.getElem_mem hq
    obtain ⟨D, hDmem, hdrStep⟩ := List.mem_flatMap.mp hdrMem
    obtain ⟨j, hD⟩ := List.mem_iff_getElem?.mp hDmem
    obtain ⟨rIdx, hdr⟩ := List.mem_iff_getElem?.mp hdrStep
    obtain ⟨_, _, fr, _, _, hweiEq, hpkEq, hwcEq, hsigEq, hfullAt⟩ :=
      step_request_correspondence v j D hD rIdx dr hdr
    rw [hdrIdx, hdatSome, Option.some.injEq] at hfullAt
    unfold frameDepositData at hfullAt
    simp only [Prod.mk.injEq] at hfullAt
    obtain ⟨hpkFr, hwcFr, hsigFr, hamtFr⟩ := hfullAt
    have hamtEq : dr.amount.toNat = amtGwei := by
      have hdiv : fr.sevm.value.toNat / BeaconDeposit.oneGwei = dr.amount.toNat := by
        rw [← hweiEq]; exact Nat.mul_div_cancel _ (by decide : 0 < 10 ^ 9)
      exact hdiv.symm.trans hamtFr.symm
    let d := requestPending dr D.block.2.message.slot
    have hinReq : (some k, d) ∈ v.ingress.steps.flatMap requestEntries := by
      refine List.mem_flatMap.mpr ⟨D, hDmem, List.mem_map.mpr ⟨dr, hdrStep, ?_⟩⟩
      simp only [hdrIdx]
      rfl
    exact Or.inr ⟨hnoPre, d, List.mem_append_right _ hinReq,
      hpkEq.trans hpkFr.symm, hwcEq.trans hwcFr.symm, hsigEq.trans hsigFr.symm, hamtEq,
      v.stepsPostGenesis D hDmem⟩

end Blanc.Composition.DepositJoint
