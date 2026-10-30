import Blanc.Lift.Curve3Crv.FrameReplay
import Blanc.ExecutionAccountingHistoryIn
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionHistoricalLadder
import Blanc.ExecutionStagedFrameEnv
import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionRewardCredits

/-!
# Curve history over historical forks, identified with its committed writer invocations

The counterpart of `c3crv_history_committed_derived` (`CommittedHistory.lean`) for a configured
history `ConfiguredHistoryTraceIn HistFork`, and for a mid history starting right after one
transaction of a retained block (`MidHistoryTraceIn HistFork`, the creation-block shape S4 needs).

The frame obligations are the modern ones read from `rules.stateGas = none` alone:
`c3crv_frame_refines_rawH`, `c3crv_writer_nonstaticH` (`Safe.lean`) and
`target_committedFrameInvocationsIn` (`CommittedExec.lean`). The one change of statement is the
owner evidence: a historical frame's `owner()` static call resolves its callee's code under the
frame's actual delegation rules (`StaticAnsweredH`), so the model steps carry `OwnerAnswerH`
(`InvRunBy OwnerAnswerH`); on a covered fork it is `OwnerAnswer` (`OwnerAnswerH.of_covered`).

The ladder is `coreAccountingIn` over any domain without state gas (`curveAccountingLadderIn`);
the headlines are its `HistFork` instances, with the calldata bound derived from the retained
transactions (`frameAdmitted_calldata_hist`, `MidHistoryTraceIn.calldata_bound`).
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- The settlement-committed writer invocations at the contract of a selected-domain history, in
trace order. -/
def committedInvocationsIn {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    List WriterInvocation :=
  trace.settledFrames.flatMap (committedFrameInvocations ca)

/-- Keys read or written by the actual raw target entries of a selected-domain history, including
failed or later rolled-back branches. -/
def historyTouchedKeysIn {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) : List Key :=
  trace.rawFrames.flatMap fun root =>
    if root.sevm.currentTarget = ca then callKeys root.sevm.caller (decodeCall root.sevm) else []

/-- The keys the actual raw target entries of a mid history may touch, including entries whose
effects later roll back. -/
def midTouchedKeysIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (ca : Adr) (trace : MidHistoryTraceIn F cfg start future) :
    List Key :=
  trace.rawFrames.flatMap fun root =>
    if root.sevm.currentTarget = ca then callKeys root.sevm.caller (decodeCall root.sevm) else []

/-- The settlement-committed writer invocations at the contract of a mid history, in trace
order. -/
def midCommittedInvocationsIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (ca : Adr) (trace : MidHistoryTraceIn F cfg start future) :
    List WriterInvocation :=
  trace.settledFrames.flatMap (committedFrameInvocations ca)

/-- The checked installed runtime supplies historical settlement's no-deletion producer: its
certificate executes only `STATICCALL` and no `SELFDESTRUCT`. -/
theorem c3crvInstalledCert : InstalledCert code where
  exists_cert := ⟨cert, cert_check, by decide +kernel, by decide +kernel⟩
  notDelegation := c3crvSem.not_delegation rfl
  nonempty := by
    intro empty
    have length := code_toList_length
    rw [empty] at length
    cases length

private theorem target_replayIn {ca : Adr} {U : Key → Prop}
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots)
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (admitted : Exec.FrameAdmitted ca (carriedFrameEntry U) run)
    (nodes : (Exec.committedFrames run).flatMap (committedFrameInvocations ca) =
      committedFrameInvocations ca (Exec.Frame.ofRun run committed)) :
    (sevm.isStatic = true →
      (Exec.committedFrames run).flatMap (committedFrameInvocations ca) = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      (curveFrameCarrierBy OwnerAnswerH ca U).Replay
        ((curveFrameCarrierBy OwnerAnswerH ca U).frameEntry sevm pre.state) steps
        ((curveFrameCarrierBy OwnerAnswerH ca U).ofState
          (Execution.committedPost (.ok post) committed).state) ∧
      (curveFrameObservationBy OwnerAnswerH ca U).obs steps =
        (Exec.committedFrames run).flatMap (committedFrameInvocations ca)) := by
  obtain ⟨⟨hstack, hmem⟩, hcd, touched⟩ := admitted.root target
  have self : committedFrameInvocations ca (Exec.Frame.ofRun run committed) =
      if IsWriter (decodeCall sevm) then [⟨sevm, pre, post, ownerWordOf sevm⟩] else [] := by
    show (if sevm.currentTarget = ca ∧ IsWriter (decodeCall sevm) then
        [frameInvocation (Exec.Frame.ofRun run committed)] else []) = _
    by_cases h : IsWriter (decodeCall sevm)
    · simp only [target, h, and_self, ↓reduceIte]
      rfl
    · simp only [h, and_false, ↓reduceIte]
  refine ⟨fun static => ?_, fun _ => ?_⟩
  · have quiet : ¬ IsWriter (decodeCall sevm) := fun writer => by
      rw [c3crv_writer_nonstaticH hcode hsg hcd hstack hmem run writer] at static
      cases static
    rw [nodes, self]
    simp only [quiet, ↓reduceIte]
  · by_cases writer : IsWriter (decodeCall sevm)
    · refine ⟨[⟨sevm, pre, post, ownerWordOf sevm⟩], ?_,
        by rw [nodes, self]; simp only [writer, ↓reduceIte]; rfl⟩
      change CurveFrameReplayBy OwnerAnswerH ca U (Devm.getStor pre ca)
        ([⟨sevm, pre, post, ownerWordOf sevm⟩] : List WriterInvocation) (Devm.getStor post ca)
      refine ⟨?_, fun s K included invariant => ?_⟩
      · intro k hk
        rw [invocationKeys_singleton] at hk
        exact touched k (by simpa only [target] using hk)
      · subst target
        have fresh := FreshKeys.of_universe injective apart included touched
        obtain ⟨ow, owner, out, accepted, invariant', _⟩ :=
          (c3crv_frame_refines_rawH hcode hsg hcd hstack hmem invariant fresh run).1 writer
        obtain ⟨accepted', canonical⟩ := step_ownerWordOf accepted
        exact CurveFrameReplayBy.singleton ⟨accepted', fun w h => owner w (canonical w h)⟩
          included touched fresh invariant invariant'
    · refine ⟨[], ?_, by rw [nodes, self]; simp only [writer, ↓reduceIte]; rfl⟩
      change CurveFrameReplayBy OwnerAnswerH ca U (Devm.getStor pre ca) [] (Devm.getStor post ca)
      refine ⟨(CurveReplayBy.nil OwnerAnswerH U Stor.empty).1, fun s K included invariant =>
        ⟨s, rfl, (fun _ h => by cases h), ?_⟩⟩
      simp only [invocationKeys, List.flatMap_nil, Key.extend_nil]
      subst target
      have fresh := FreshKeys.of_universe injective apart included touched
      have refinement := c3crv_frame_refines_rawH hcode hsg hcd hstack hmem invariant fresh run
      exact invariant.of_get_eq fun x => by
        rw [(refinement.2 writer).1 sevm.currentTarget]

private theorem curve_coreIn (F : Fork → Prop)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    Exec.Fa (Exec.WknSem ca c3crvSem
      (fun pc s d e _ => Blanc.Exec.CoreAccountingIn F ca c3crvSem (carriedFrameEntry U)
        (curveFrameCarrierBy OwnerAnswerH ca U) (curveFrameObservationBy OwnerAnswerH ca U)
          pc s d e)) := by
  apply Blanc.Exec.coreAccountingIn F ca c3crvSem (carriedFrameEntry U)
    (curveFrameCarrierBy OwnerAnswerH ca U) (curveFrameObservationBy OwnerAnswerH ca U)
    CurveFrameReplayBy.append (fun _ _ => ())
  · intro sevm state foreign
    rfl
  · intro frame foreign
    change committedFrameInvocations ca frame = []
    simp only [committedFrameInvocations, foreign, false_and, ↓reduceIte]
  · exact hsgF
  · intro sevm pre post hcode target deeper run committed fork installed admitted
    apply target_replayIn injective apart run committed hcode target (hsgF fork) admitted
    apply target_committedFrameInvocationsIn (F := F) run committed hcode target installed fork
      (hsgF fork) admitted
    intro pc s d out child childCommitted childFork depth childAt childAdmitted static
    exact (deeper pc s d out child depth childAt
      child childCommitted childFork childAt childAdmitted).1 static

/-- The accounting ladder of the Curve committed replay over a fork domain without state gas,
over a collision universe `U` with injective slots apart from the fixed ones. -/
def curveAccountingLadderIn (F : Fork → Prop)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    AccountingLadderAdmittedIn F (curveSpec U) ca (carriedFrameEntry U) where
  carrier := curveFrameCarrierBy OwnerAnswerH ca U
  append := CurveFrameReplayBy.append
  tag := fun _ _ => ()
  preserves := curveSpec_preservesAdmittedIn F hsgF ca U injective apart
  view := curveFrameObservationBy OwnerAnswerH ca U
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed
      admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ :=
      Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (curve_coreIn F hsgF ca U injective apart pc sevm pre out run installed
      run committed fork installed admitted).2 entryBound

/-- **The Curve model replays the committed chain of a historical history.** The statement of
`c3crv_history_committed_derived` for a configured history over the historical domain `HistFork`
(Byzantium through BPO2): from the installed runtime, one initial model abstraction `VyInv` over
`initialKeys`, and the trace-local freshness of the keys the actual raw target entries touch, the
code stays installed and the future storage abstracts the model state obtained by running
`Curve3Crv.step` over exactly the settlement-committed writer invocations at the contract in trace
order, each accepted with the owner word the frame's actual `owner()` static call answered
(`OwnerAnswerH`, under the frame's own delegation rules); the model state conserves supply. The
per-frame calldata bound is derived from the retained transactions. -/
theorem c3crv_history_committedHist {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeysIn ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRunBy OwnerAnswerH initial (committedInvocationsIn ca trace) s ∧
        runInvocations initial (committedInvocationsIn ca trace) = some s ∧
        VyInv (future.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (committedInvocationsIn ca trace))) ∧
        Blanc.Curve3Crv.Conserved s := by
  let U := Key.extend initialKeys (historyTouchedKeysIn ca trace)
  have topology : VyInv (checkpoint.state.getStor ca) initial U := invariant.extend fresh
  have capabilities := BodyStageCapabilities.historical
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) := by
    have calldata := trace.frameAdmitted_calldata_hist (ca := ca) capabilities
    have touched : trace.FrameAdmitted ca
        (fun sevm _ => ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k) := by
      apply (trace.frameAdmitted_iff_rawFrames ca _).2
      intro root member target k hk
      exact Or.inr (List.mem_flatMap.mpr ⟨root, member, by simpa only [target, ite_true] using hk⟩)
    exact (trace.freshFrameAdmitted ca).and (calldata.and touched)
  have start : (curveSpec U).StateInv ca checkpoint.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  have rewards := trace.rewardCreditsFunded capabilities
  have finish := trace.stateInv_admitted_semIn
    (curveSpec_preservesAdmittedIn HistFork HistFork.stateGas_none ca U topology.inj
      topology.apart) capabilities admitted rewards start
    c3crvInstalledCert rfl
  obtain ⟨steps, replay, observed⟩ :=
    (curveAccountingLadderIn HistFork HistFork.stateGas_none ca U topology.inj
      topology.apart).configuredHistoryIn trace admitted capabilities rewards start c3crvInstalledCert rfl
  change CurveFrameReplayBy OwnerAnswerH ca U (checkpoint.state.getStor ca) steps
    (future.state.getStor ca) at replay
  change steps = committedInvocationsIn ca trace at observed
  subst observed
  obtain ⟨s, run, -, final⟩ := replay.2 initial initialKeys (fun _ hk => Or.inl hk) invariant
  exact ⟨finish.code, s, run, run.runInvocations_eq, final, final.conserved⟩

/-- **The committed chain of a historical mid history, frame by frame.** As
`c3crv_mid_history_committedHist`, and also: every committed writer invocation's own opening and
closing storage abstract the model step it runs (`FrameModelBy`, over the collision universe of the
initial live keys and the keys the raw target entries touch), and the invocations' keys lie in that
universe. -/
theorem c3crv_mid_history_framesHist {ca : Adr} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (start.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (midTouchedKeysIn ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRunBy OwnerAnswerH initial (midCommittedInvocationsIn ca trace) s ∧
        (∀ inv ∈ midCommittedInvocationsIn ca trace,
          FrameModelBy OwnerAnswerH ca (Key.extend initialKeys (midTouchedKeysIn ca trace)) inv) ∧
        VyInv (future.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (midCommittedInvocationsIn ca trace))) ∧
        ∀ k ∈ invocationKeys (midCommittedInvocationsIn ca trace),
          Key.extend initialKeys (midTouchedKeysIn ca trace) k := by
  let U := Key.extend initialKeys (midTouchedKeysIn ca trace)
  have topology : VyInv (start.state.getStor ca) initial U := invariant.extend fresh
  have capabilities := BodyStageCapabilities.historical
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target
    refine ⟨trace.rawFrames_entered enteredCondition_fresh root member,
      trace.calldata_bound capabilities (fun _ hf => hf.dataNonZero_ge) root member,
      fun k hk => Or.inr ?_⟩
    exact List.mem_flatMap.mpr ⟨root, member, by simpa only [target, ite_true] using hk⟩
  have startInv : (curveSpec U).StateInv ca start.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  have rewards := trace.rewardCreditsFunded capabilities
  have finish := trace.stateInv_admitted_semIn
    (curveSpec_preservesAdmittedIn HistFork HistFork.stateGas_none ca U topology.inj
      topology.apart) capabilities admitted rewards startInv
    c3crvInstalledCert rfl
  obtain ⟨steps, replay, observed⟩ :=
    (curveAccountingLadderIn HistFork HistFork.stateGas_none ca U topology.inj
      topology.apart).midHistoryIn trace admitted capabilities rewards startInv c3crvInstalledCert rfl
  change CurveFrameReplayBy OwnerAnswerH ca U (start.state.getStor ca) steps
    (future.state.getStor ca) at replay
  change steps = midCommittedInvocationsIn ca trace at observed
  subst observed
  obtain ⟨s, run, frames, final⟩ := replay.2 initial initialKeys (fun _ hk => Or.inl hk) invariant
  exact ⟨finish.code, s, run, frames, final, replay.1⟩

/-- **The Curve model replays the committed chain of a historical mid history**, one that starts
right after a transaction of a retained `HistFork` block (`MidHistoryTraceIn`): the statement of
`c3crv_history_committedHist` from the state `start` after that transaction. -/
theorem c3crv_mid_history_committedHist {ca : Adr} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (start.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (midTouchedKeysIn ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRunBy OwnerAnswerH initial (midCommittedInvocationsIn ca trace) s ∧
        runInvocations initial (midCommittedInvocationsIn ca trace) = some s ∧
        VyInv (future.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (midCommittedInvocationsIn ca trace))) ∧
        Blanc.Curve3Crv.Conserved s := by
  obtain ⟨code, s, run, -, final, -⟩ := c3crv_mid_history_framesHist trace installed invariant fresh
  exact ⟨code, s, run, run.runInvocations_eq, final, final.conserved⟩

end Blanc.Lift.Curve3Crv
