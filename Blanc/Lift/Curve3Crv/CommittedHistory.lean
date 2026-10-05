import Blanc.Lift.Curve3Crv.CommittedExec
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionAccountingCore
import Blanc.ExecutionTraceCalldata

/-!
# Curve history identified with its committed writer invocations

Curve is the second consumer of the generic accounting ladder
(`Exec.coreAccounting`, `AccountingLadderAdmitted.configuredHistory`), after the
beacon deposit contract. The replay boundary is the contract's storage; the
observation is the ordered list of committed writer invocations at the contract
address (each non-static by `c3crv_writer_nonstatic`, not by filtering). Frame
chaining, interpreter ingress, foreign movements and rollback are derived by the ladder; only the target frame's refinement
(`c3crv_frame_refines_raw`) and the static-only spawn restriction are Curve's own.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- The frame contract over a fixed collision universe: the storage abstracts some
model state whose live keys lie in `U`. -/
def curveSpec (U : Key → Prop) : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly c3crvSem
    (fun stor => ∃ s K, (∀ k, K k → U k) ∧ VyInv stor s K)

theorem curveSpec_soundAdmitted (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    (curveSpec U).SoundAdmitted ca (carriedFrameEntry U) := by
  intro sevm pre post hfork execution deployed target admitted _ _ incoming
  subst target
  obtain ⟨⟨hstack, hmem⟩, hcd, touched⟩ := admitted.root rfl
  obtain ⟨s, K, included, invariant⟩ :
      ∃ s K, (∀ k, K k → U k) ∧ VyInv (Devm.getStor pre sevm.currentTarget) s K :=
    ContractSpecSem.ofStorageOnly_preInv_iff.mp incoming.inv
  have fresh := FreshKeys.of_universe injective apart included touched
  have refinement := c3crv_frame_refines_raw deployed hfork hcd hstack hmem invariant fresh
    execution
  refine ⟨trivial, ?_⟩
  show ∃ s K, (∀ k, K k → U k) ∧ VyInv (Devm.getStor post sevm.currentTarget) s K
  by_cases writer : IsWriter (decodeCall sevm)
  · obtain ⟨_, _, out, _, invariant', _⟩ := refinement.1 writer
    exact ⟨out.1, _, fun k hk => hk.elim (included k) (touched k), invariant'⟩
  · refine ⟨s, K, included, ?_⟩
    rw [(refinement.2 writer).1 sevm.currentTarget]
    exact invariant

theorem curveSpec_preservesAdmitted (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    (curveSpec U).PreservesAdmitted ca (carriedFrameEntry U) :=
  (curveSpec U).preserves_inv_admitted ca (carriedFrameEntry U)
    (curveSpec_soundAdmitted ca U injective apart)

private theorem target_replay {ca : Adr} {U : Key → Prop}
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots)
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca (carriedFrameEntry U) run)
    (nodes : (Exec.committedFrames run).flatMap (committedFrameInvocations ca) =
      committedFrameInvocations ca (Exec.Frame.ofRun run committed)) :
    (sevm.isStatic = true →
      (Exec.committedFrames run).flatMap (committedFrameInvocations ca) = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      (curveCarrier ca U).Replay ((curveCarrier ca U).frameEntry sevm pre.state) steps
        ((curveCarrier ca U).ofState (Execution.committedPost (.ok post) committed).state) ∧
      (curveObservation ca U).obs steps =
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
      rw [c3crv_writer_nonstatic hcode fork hcd hstack hmem run writer] at static
      cases static
    rw [nodes, self]
    simp only [quiet, ↓reduceIte]
  · by_cases writer : IsWriter (decodeCall sevm)
    · refine ⟨[⟨sevm, pre, post, ownerWordOf sevm⟩], ?_, by rw [nodes, self]; simp only [writer, ↓reduceIte]; rfl⟩
      change CurveReplay U (Devm.getStor pre ca)
        ([⟨sevm, pre, post, ownerWordOf sevm⟩] : List WriterInvocation) (Devm.getStor post ca)
      refine ⟨?_, fun s K included invariant => ?_⟩
      · intro k hk
        rw [invocationKeys_singleton] at hk
        exact touched k (by simpa only [target] using hk)
      · subst target
        have fresh := FreshKeys.of_universe injective apart included touched
        obtain ⟨ow, owner, out, accepted, invariant', _⟩ :=
          (c3crv_frame_refines_raw hcode fork hcd hstack hmem invariant fresh run).1 writer
        obtain ⟨accepted', canonical⟩ := step_ownerWordOf accepted
        refine ⟨out.1, ⟨out, ⟨accepted', fun w h => ?_⟩, rfl⟩, ?_⟩
        · have := canonical w h
          exact owner w this
        · simpa only [invocationKeys_singleton] using invariant'
    · refine ⟨[], ?_, by rw [nodes, self]; simp only [writer, ↓reduceIte]; rfl⟩
      change CurveReplay U (Devm.getStor pre ca) [] (Devm.getStor post ca)
      refine ⟨by simp only [invocationKeys, List.flatMap_nil, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true], fun s K included invariant => ⟨s, rfl, ?_⟩⟩
      simp only [invocationKeys, List.flatMap_nil, Key.extend_nil]
      subst target
      have fresh := FreshKeys.of_universe injective apart included touched
      have refinement := c3crv_frame_refines_raw hcode fork hcd hstack hmem invariant fresh run
      exact invariant.of_get_eq fun x => by
        rw [(refinement.2 writer).1 sevm.currentTarget]

private theorem curve_core (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    Exec.Fa (Exec.WknSem ca c3crvSem
      (fun pc s d e _ => Blanc.Exec.CoreAccounting ca c3crvSem (carriedFrameEntry U)
        (curveCarrier ca U) (curveObservation ca U) pc s d e)) := by
  apply Blanc.Exec.coreAccounting ca c3crvSem (carriedFrameEntry U)
    (curveCarrier ca U) (curveObservation ca U) CurveReplay.append (fun _ _ => ())
  · intro sevm state foreign
    rfl
  · intro frame foreign
    change committedFrameInvocations ca frame = []
    simp only [committedFrameInvocations, foreign, false_and, ↓reduceIte]
  · intro sevm pre post hcode target deeper run committed fork installed admitted
    apply target_replay injective apart run committed hcode target fork admitted
    apply target_committedFrameInvocations run committed hcode target installed fork admitted
    intro pc s d out child childCommitted childFork depth childAt childAdmitted static
    exact (deeper pc s d out child depth childAt
      child childCommitted childFork childAt childAdmitted).1 static

private def curveAccountingLadder (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    AccountingLadderAdmitted (curveSpec U) ca (carriedFrameEntry U) where
  carrier := curveCarrier ca U
  append := CurveReplay.append
  tag := fun _ _ => ()
  preserves := curveSpec_preservesAdmitted ca U injective apart
  view := curveObservation ca U
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed
      admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ :=
      Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (curve_core ca U injective apart pc sevm pre out run installed
      run committed fork installed admitted).2 entryBound

/-- **The Curve model replays the committed chain.** In a configured history the
deployed 3Crv runtime's final storage abstracts the model state obtained by running
`Curve3Crv.step`, from the initial model state, over exactly the writer invocations
of the settlement-committed frames at the contract address, in trace order
(`committedInvocations`): rolled-back frames do not appear, views contribute
nothing, and no static frame is filtered out, because a writer cannot succeed in a
static frame (`c3crv_writer_nonstatic`). Each invocation carries its frame's own
caller and calldata (`c3ctx`, `decodeCall`), and each step is accepted by the model with the owner word
the frame's actual `owner()` static call answered (`ModelStep`). The live keys are the
initial keys plus the keys of exactly those invocations. The list is definitional, not
chosen; the model state is its fold (`runInvocations`).

The collision premise covers the initial keys and all actual raw target entries,
including rolled-back branches. Initial storage/code authentication and the truth of
collision separation remain premises. Interpreter ingress, non-target movements,
static owner queries (which may re-enter the contract read-only) and rollback are
discharged by the accounting ladder. -/
theorem c3crv_history_committed {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRun initial (committedInvocations ca trace) s ∧
        runInvocations initial (committedInvocations ca trace) = some s ∧
        VyInv (future.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
        Blanc.Curve3Crv.Conserved s := by
  let U := historyKeyUniverse ca trace initialKeys
  have topology : VyInv (checkpoint.state.getStor ca) initial U := invariant.extend fresh
  have touched : trace.FrameAdmitted ca
      (fun sevm _ => ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) :=
    (trace.freshFrameAdmitted ca).and (calldata.and touched)
  have start : (curveSpec U).StateInv ca checkpoint.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  have finish := trace.stateInv_admitted_sem
    (curveSpec_preservesAdmitted ca U topology.inj topology.apart) admitted start
  obtain ⟨steps, replay, observed⟩ :=
    (curveAccountingLadder ca U topology.inj topology.apart).configuredHistory trace admitted start
  change CurveReplay U (checkpoint.state.getStor ca) steps (future.state.getStor ca) at replay
  change steps = committedInvocations ca trace at observed
  subst observed
  obtain ⟨s, run, final⟩ := replay.2 initial initialKeys (fun _ hk => Or.inl hk) invariant
  exact ⟨finish.code, s, run, run.runInvocations_eq, final, final.conserved⟩

/-- **`c3crv_history_committed` without the calldata premise.**  The per-frame calldata bound
follows from the retained transaction and header validation
(`ConfiguredHistoryTrace.frameAdmitted_calldata`), so the headline keeps only the collision
premise. -/
theorem c3crv_history_committed_derived {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRun initial (committedInvocations ca trace) s ∧
        runInvocations initial (committedInvocations ca trace) = some s ∧
        VyInv (future.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
        Blanc.Curve3Crv.Conserved s :=
  c3crv_history_committed trace installed invariant trace.frameAdmitted_calldata fresh

end Blanc.Lift.Curve3Crv
