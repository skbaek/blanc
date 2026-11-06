import Blanc.Composition.Curve3CrvTokenCore
import Blanc.ExecutionAccountingPositionalHistory
import Blanc.ExecutionWholeFrameAccounting
import Blanc.Lift.Curve3Crv.HistFrameReady
import Blanc.Lift.RetainedTargetCompleteness

/-!
# 3Crv's positional replay over a configured history (U8b, R3 option (b))

3Crv's own ladder pieces (`curve_core`, `curveAccountingLadder`, `target_replay`) are private to
`Lift/Curve3Crv/CommittedHistory.lean`, so the positional ladder is rebuilt here from public pieces
(`CurveReplayBy`, `curveSpec_preservesAdmitted`, `c3crv_frame_refines_raw`, `step_ownerWordOf`,
`parentPrefix_exec_staticcall_of_cert`), without editing a Curve3Crv file:

* the boundary is the **word view** of 3Crv's storage (`View`, `viewOf`), so it is a function of the
  storage words (`ofStateGet`, which raw `Stor` equality is not);
* the replay is `CurveReplayBy` between any storages realising the two views (`ViewReplayBy`), since
  `VyInv` reads storage only through its words (`VyInv.of_get_eq`);
* the observation is the committed writer invocation of each **non-static** settled frame at the
  address (`viewFrameObs`): static frames contribute nothing (a writer cannot succeed static);
* the target obligation is the whole-frame one (`c3crv_wholeFrameBy`): a 3Crv frame's only spawned
  frames are static `owner()` queries (the certificate executes no external instruction but
  `STATICCALL`, `cert_onlyStaticcall`), so its subtree observes exactly its own invocation.

The carrier, the observation and the obligation take the owner evidence `A`: `OwnerAnswer` for the
pinned `c3crv_history_at`, `OwnerAnswerH` for the supply walk (`Curve3PoolSupply*`), on configured and
historical histories alike.

`c3crv_history_at` is the positional headline of `wholeFramePositionalLadder`: at the entry of every
settled frame not enclosed by an earlier non-static 3Crv frame, 3Crv's storage abstracts the model
fold of the committed invocations before it.  Positions inside a non-static 3Crv frame (only the
`owner()` subtree of `set_name`) are excluded: 3Crv's storage there is not proved to be a replay
boundary from public statements.
-/

namespace Blanc.Composition.Curve3CrvToken

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay

/-! ## The word-view carrier -/

/-- A storage word view that some storage realises. -/
def View : Type := {f : B256 → B256 // ∃ stor : Stor, stor.get = f}

/-- The word view of a storage. -/
def viewOf (stor : Stor) : View := ⟨stor.get, stor, rfl⟩

theorem curveReplay_congr {A : Sevm → Devm → Adr → B256 → Prop} {U : Key → Prop}
    {pre pre' post post' : Stor} {invs : List WriterInvocation} (h : CurveReplayBy A U pre invs post)
    (hpre : ∀ x, pre'.get x = pre.get x) (hpost : ∀ x, post'.get x = post.get x) :
    CurveReplayBy A U pre' invs post' := by
  refine ⟨h.1, fun s K hK hv => ?_⟩
  obtain ⟨s', run, inv'⟩ := h.2 s K hK (hv.of_get_eq fun x => (hpre x).symm)
  exact ⟨s', run, inv'.of_get_eq hpost⟩

/-- `CurveReplayBy` between any storages realising the two views, under the answer predicate `A`. -/
def ViewReplayBy (A : Sevm → Devm → Adr → B256 → Prop) (U : Key → Prop) (a : View)
    (invs : List WriterInvocation) (b : View) : Prop :=
  ∀ pre post : Stor, pre.get = a.1 → post.get = b.1 → CurveReplayBy A U pre invs post

/-- `ViewReplayBy` with the modern owner evidence. -/
abbrev ViewReplay (U : Key → Prop) (a : View) (invs : List WriterInvocation) (b : View) : Prop :=
  ViewReplayBy OwnerAnswer U a invs b

theorem viewReplay_nil (A : Sevm → Devm → Adr → B256 → Prop) (U : Key → Prop) (a : View) :
    ViewReplayBy A U a [] a := by
  intro pre post hpre hpost
  exact curveReplay_congr (CurveReplayBy.nil A U pre) (fun _ => rfl) fun x => by rw [hpost, ← hpre]

theorem viewReplay_append {A : Sevm → Devm → Adr → B256 → Prop} {U : Key → Prop} {a b c : View}
    {xs ys : List WriterInvocation}
    (first : ViewReplayBy A U a xs b) (second : ViewReplayBy A U b ys c) :
    ViewReplayBy A U a (xs ++ ys) c := by
  intro pre post hpre hpost
  obtain ⟨mid, hmid⟩ := b.2
  exact (first pre mid hpre hmid).append (second mid post hmid hpost)

theorem viewReplay_of {A : Sevm → Devm → Adr → B256 → Prop} {U : Key → Prop} {pre post : Stor}
    {invs : List WriterInvocation} (h : CurveReplayBy A U pre invs post) :
    ViewReplayBy A U (viewOf pre) invs (viewOf post) := by
  intro pre' post' hpre hpost
  exact curveReplay_congr h (fun x => congrFun hpre x) fun x => congrFun hpost x

/-- The word-view replay carrier of 3Crv over the collision universe `U`. -/
def viewCarrierBy (A : Sevm → Devm → Adr → B256 → Prop) (ca : Adr) (U : Key → Prop) :
    ReplayCarrier ca where
  readsStorage := true
  Snap := View
  Step := WriterInvocation
  Tag := Unit
  Replay := ViewReplayBy A U
  ofState state := viewOf (state.getStor ca)
  frameEntry _ state := viewOf (state.getStor ca)
  nil := viewReplay_nil A U
  silent := fun storage _ => by rw [storage rfl]
  credit := by
    intro _ _ _ _ storage _ _
    exact ⟨[], by rw [storage]; exact viewReplay_nil A U _⟩
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    exact congrArg viewOf (benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun transfers _ => Or.inl (caller_ne transfers)))

/-- The committed writer invocation of a non-static settled frame at the address. -/
def viewFrameObs (ca : Adr) (f : Exec.Frame) : List WriterInvocation :=
  if f.sevm.isStatic = false then committedFrameInvocations ca f else []

theorem viewFrameObs_static {ca : Adr} {f : Exec.Frame} (h : f.sevm.isStatic = true) :
    viewFrameObs ca f = [] := by
  simp only [viewFrameObs, h, Bool.true_eq_false, ↓reduceIte]

theorem viewFrameObs_foreign {ca : Adr} {f : Exec.Frame} (h : f.sevm.currentTarget ≠ ca) :
    viewFrameObs ca f = [] := by
  unfold viewFrameObs committedFrameInvocations
  simp only [h, false_and, ↓reduceIte, ite_self]

/-- The ordered observation: the committed writer invocations of non-static frames. -/
def viewObservationBy (A : Sevm → Devm → Adr → B256 → Prop) (ca : Adr) (U : Key → Prop) :
    ReplayObservation (viewCarrierBy A ca U) where
  O := WriterInvocation
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := viewFrameObs ca
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change ViewReplayBy A U (viewOf (pre.getStor ca)) [] (viewOf (post.getStor ca))
    rw [storage]
    exact viewReplay_nil A U _

/-! ## The target obligations -/

/-- 3Crv frames spawn only by `STATICCALL`. -/
theorem c3crv_spawnKinds (ca : Adr) : SpawnKinds ca c3crvSem := by
  intro sevm pre post _ hrun _ fork _ node chain x instruction
  exact .inr (parentPrefix_exec_staticcall_of_cert cert_check cert_onlyStaticcall
    (root := ⟨0, sevm, pre, .ok post, _⟩) rfl hrun fork chain instruction)

/-- The raw refinement of 3Crv's runtime on the fork domain `F`, under the answer predicate `A`:
`c3crv_frame_refines_raw` with `OwnerAnswer` on the covered forks, `c3crv_frame_refines_rawH` with
`OwnerAnswerH` on any domain without state gas. -/
def FrameRefines (A : Sevm → Devm → Adr → B256 → Prop) (F : Fork → Prop) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} {s : Blanc.Curve3Crv.State} {K : Key → Prop},
    sevm.code = code → F sevm.benvStat.fork → sevm.data.length < 2 ^ 256 → pre.stack = [] →
    pre.memory = Mem.empty → VyInv (Devm.getStor pre sevm.currentTarget) s K →
    FreshKeys K (callKeys sevm.caller (decodeCall sevm)) → Exec 0 sevm pre (.ok post) →
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → A sevm pre s.minter w) ∧
        ∃ o, Blanc.Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm)))) ∧
    (¬ IsWriter (decodeCall sevm) → ∀ a, Devm.getStor post a = Devm.getStor pre a)

theorem frameRefines_covered : FrameRefines OwnerAnswer CoveredFork := by
  intro _ _ _ _ _ hcode fork hcd hstack hmem hinv hfresh run
  have r := c3crv_frame_refines_raw hcode fork hcd hstack hmem hinv hfresh run
  refine ⟨fun writer => ?_, fun writer => (r.2 writer).1⟩
  obtain ⟨ow, owner, o, accepted, invariant, -⟩ := r.1 writer
  exact ⟨ow, owner, o, accepted, invariant⟩

theorem frameRefines_noStateGas {F : Fork → Prop}
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) : FrameRefines OwnerAnswerH F := by
  intro _ _ _ _ _ hcode fork hcd hstack hmem hinv hfresh run
  have r := c3crv_frame_refines_rawH hcode (hsgF fork) hcd hstack hmem hinv hfresh run
  refine ⟨fun writer => ?_, fun writer => (r.2 writer).1⟩
  obtain ⟨ow, owner, o, accepted, invariant, -⟩ := r.1 writer
  exact ⟨ow, owner, o, accepted, invariant⟩

/-- **The whole-frame obligation**: a committed non-static 3Crv frame replays, from its entry view
to its post view, with exactly the observation of its committed subtree, which is its own
invocation. -/
theorem c3crv_wholeFrameBy {A : Sevm → Devm → Adr → B256 → Prop} {F : Fork → Prop}
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) (refines : FrameRefines A F)
    (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    Exec.CoreAccounting.WholeFrameReplayIn F ca c3crvSem (carriedFrameEntry U) (viewCarrierBy A ca U)
      (viewObservationBy A ca U) := by
  intro sevm pre post run committed hcode target fork installed admitted _ nonstatic
  obtain ⟨⟨hstack, hmem⟩, hcd, touched⟩ := admitted.root target
  have descendants : (Exec.descendantFrames run).flatMap (viewFrameObs ca) = [] :=
    Exec.staticOnly_descendantFrames_flatMap_eq_nilIn (F := F) ca c3crvSem (carriedFrameEntry U)
      (viewFrameObs ca) ⟨0, sevm, pre, .ok post, run⟩ target installed.1 fork
      (fun chain instruction =>
        parentPrefix_exec_staticcall_of_cert_noStateGas cert_check cert_onlyStaticcall
          (root := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode (hsgF fork) chain instruction)
      (fun child _ _ _ _ _ static => List.flatMap_eq_nil_iff.mpr fun D member =>
        viewFrameObs_static (Blanc.Exec.committedFrames_isStatic child static D member))
      run (.refl _) (by
        intro frameRoot member selected
        exact admitted frameRoot (List.mem_cons_of_mem _ member) selected)
  have whole : (Exec.committedFrames run).flatMap (viewFrameObs ca) =
      if IsWriter (decodeCall sevm) then [⟨sevm, pre, post, ownerWordOf sevm⟩] else [] := by
    rw [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons, descendants,
      List.append_nil]
    show (if sevm.isStatic = false then
        (if sevm.currentTarget = ca ∧ IsWriter (decodeCall sevm) then
          [frameInvocation (Exec.Frame.ofRun run committed)] else []) else []) = _
    by_cases writer : IsWriter (decodeCall sevm)
    · simp only [nonstatic, target, writer, and_self, ↓reduceIte]
      rfl
    · simp only [nonstatic, writer, and_false, ↓reduceIte]
  subst target
  by_cases writer : IsWriter (decodeCall sevm)
  · let invs : List WriterInvocation := [⟨sevm, pre, post, ownerWordOf sevm⟩]
    have replay : CurveReplayBy A U (Devm.getStor pre sevm.currentTarget) invs
        (Devm.getStor post sevm.currentTarget) := by
      refine ⟨?_, fun s K included invariant => ?_⟩
      · intro k hk
        rw [invocationKeys_singleton] at hk
        exact touched k hk
      · have fresh := FreshKeys.of_universe injective apart included touched
        obtain ⟨ow, owner, out, accepted, invariant'⟩ :=
          (refines hcode fork hcd hstack hmem invariant fresh run).1 writer
        obtain ⟨accepted', canonical⟩ := step_ownerWordOf accepted
        refine ⟨out.1, ⟨out, ⟨accepted', fun w h => owner w (canonical w h)⟩, rfl⟩, ?_⟩
        simpa only [invs, invocationKeys_singleton] using invariant'
    exact ⟨invs, viewReplay_of replay, (whole.trans (if_pos writer)).symm⟩
  · have replay : CurveReplayBy A U (Devm.getStor pre sevm.currentTarget) []
        (Devm.getStor post sevm.currentTarget) := by
      refine ⟨by simp only [invocationKeys, List.flatMap_nil, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true], fun s K included invariant => ⟨s, rfl, ?_⟩⟩
      simp only [invocationKeys, List.flatMap_nil, Key.extend_nil]
      have fresh := FreshKeys.of_universe injective apart included touched
      have refinement := refines hcode fork hcd hstack hmem invariant fresh run
      exact invariant.of_get_eq fun x => by
        rw [refinement.2 writer sevm.currentTarget]
    exact ⟨[], viewReplay_of replay, (whole.trans (if_neg writer)).symm⟩

/-- **3Crv's positional ladder** (whole-frame: non-static 3Crv frames are opaque), over a configured
history. -/
noncomputable def c3crvPositionalLadder (A : Sevm → Devm → Adr → B256 → Prop)
    (refines : FrameRefines A CoveredFork) (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    PositionalLadder (curveSpec U) ca (carriedFrameEntry U) :=
  wholeFramePositionalLadder (viewCarrierBy A ca U) (viewObservationBy A ca U) viewReplay_append
    (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => Subtype.ext (funext h)) (fun _ hf => viewFrameObs_static hf)
    (fun _ hf => viewFrameObs_foreign hf) (c3crv_spawnKinds ca)
    (c3crv_wholeFrameBy CoveredFork.stateGas_none refines ca U injective apart)
    (curveSpec_preservesAdmitted ca U injective apart)

/-- **3Crv's positional replay over a configured history.**  From `c3crv_history_committed_derived`'s
premises, at the entry of every settled frame `f` that no earlier non-static 3Crv frame encloses,
3Crv's storage abstracts the model fold, from the initial state, of exactly the committed writer
invocations of the non-static settled frames before `f`. -/
theorem c3crv_history_at {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false)) →
      ∃ s, InvRun initial (before.flatMap (viewFrameObs ca)) s ∧
        VyInv (f.pre.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (before.flatMap (viewFrameObs ca)))) := by
  intro before f after split noOpaque
  let U := historyKeyUniverse ca trace initialKeys
  have topology : VyInv (checkpoint.state.getStor ca) initial U := invariant.extend fresh
  have touched : trace.FrameAdmitted ca
      (fun sevm _ => ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) :=
    (trace.freshFrameAdmitted ca).and (trace.frameAdmitted_calldata.and touched)
  have start : (curveSpec U).StateInv ca checkpoint.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  obtain ⟨steps, replay, observed⟩ :=
    (c3crvPositionalLadder OwnerAnswer frameRefines_covered ca U topology.inj
      topology.apart).configuredHistory_at trace admitted
      start before f after split noOpaque
  change ViewReplay U (viewOf (checkpoint.state.getStor ca)) steps
    (viewOf (f.pre.state.getStor ca)) at replay
  change steps = before.flatMap (viewFrameObs ca) at observed
  subst observed
  obtain ⟨s, run, final⟩ := (replay _ _ rfl rfl).2 initial initialKeys (fun _ hk => Or.inl hk)
    invariant
  exact ⟨s, run, final⟩

end Blanc.Composition.Curve3CrvToken
