import Blanc.Composition.Curve3CrvTokenCore
import Blanc.ExecutionAccountingPositionalHistory
import Blanc.ExecutionWholeFrameAccounting
import Blanc.Lift.RetainedTargetCompleteness

/-!
# 3Crv's positional replay over a configured history (U8b, R3 option (b))

3Crv's own ladder pieces (`curve_core`, `curveAccountingLadder`, `target_replay`) are private to
`Lift/Curve3Crv/CommittedHistory.lean`, so the positional ladder is rebuilt here from public pieces
(`CurveReplay`, `curveSpec_preservesAdmitted`, `c3crv_frame_refines_raw`, `step_ownerWordOf`,
`parentPrefix_exec_staticcall_of_cert`), without editing a Curve3Crv file:

* the boundary is the **word view** of 3Crv's storage (`View`, `viewOf`), so it is a function of the
  storage words (`ofStateGet`, which raw `Stor` equality is not);
* the replay is `CurveReplay` between any storages realising the two views (`ViewReplay`), since
  `VyInv` reads storage only through its words (`VyInv.of_get_eq`);
* the observation is the committed writer invocation of each **non-static** settled frame at the
  address (`viewFrameObs`): static frames contribute nothing (a writer cannot succeed static);
* the target obligation is the whole-frame one (`WholeFrameReplay`): a 3Crv frame's only spawned
  frames are static `owner()` queries (the certificate executes no external instruction but
  `STATICCALL`, `c3crv_cert_staticOnly`), so its subtree observes exactly its own invocation.

`c3crv_history_at` is the positional headline of `wholeFramePositionalLadder`: at the entry of every
settled frame not enclosed by an earlier non-static 3Crv frame, 3Crv's storage abstracts the model
fold of the committed invocations before it.  Positions inside a non-static 3Crv frame (only the
`owner()` subtree of `set_name`) are excluded: 3Crv's storage there is not proved to be a replay
boundary from public statements.
-/

namespace Blanc.Composition.Curve3CrvToken

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay

/-- **The deployed 3Crv certificate executes no external instruction but `STATICCALL`**, checked
over the whole certified program at once. -/
theorem c3crv_cert_staticOnly : ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  have all : cert.prog.all (fun f => f.execsSatisfy Xinst.isStaticcall) = true := by
    decide +kernel
  exact fun f member => List.all_eq_true.mp all f member

/-! ## The word-view carrier -/

/-- A storage word view that some storage realises. -/
def View : Type := {f : B256 → B256 // ∃ stor : Stor, stor.get = f}

/-- The word view of a storage. -/
def viewOf (stor : Stor) : View := ⟨stor.get, stor, rfl⟩

theorem curveReplay_congr {U : Key → Prop} {pre pre' post post' : Stor}
    {invs : List WriterInvocation} (h : CurveReplay U pre invs post)
    (hpre : ∀ x, pre'.get x = pre.get x) (hpost : ∀ x, post'.get x = post.get x) :
    CurveReplay U pre' invs post' := by
  refine ⟨h.1, fun s K hK hv => ?_⟩
  obtain ⟨s', run, inv'⟩ := h.2 s K hK (hv.of_get_eq fun x => (hpre x).symm)
  exact ⟨s', run, inv'.of_get_eq hpost⟩

/-- `CurveReplay` between any storages realising the two views. -/
def ViewReplay (U : Key → Prop) (a : View) (invs : List WriterInvocation) (b : View) : Prop :=
  ∀ pre post : Stor, pre.get = a.1 → post.get = b.1 → CurveReplay U pre invs post

theorem viewReplay_nil (U : Key → Prop) (a : View) : ViewReplay U a [] a := by
  intro pre post hpre hpost
  exact curveReplay_congr (CurveReplay.nil U pre) (fun _ => rfl) fun x => by rw [hpost, ← hpre]

theorem viewReplay_append {U : Key → Prop} {a b c : View} {xs ys : List WriterInvocation}
    (first : ViewReplay U a xs b) (second : ViewReplay U b ys c) :
    ViewReplay U a (xs ++ ys) c := by
  intro pre post hpre hpost
  obtain ⟨mid, hmid⟩ := b.2
  exact (first pre mid hpre hmid).append (second mid post hmid hpost)

theorem viewReplay_of {U : Key → Prop} {pre post : Stor} {invs : List WriterInvocation}
    (h : CurveReplay U pre invs post) : ViewReplay U (viewOf pre) invs (viewOf post) := by
  intro pre' post' hpre hpost
  exact curveReplay_congr h (fun x => congrFun hpre x) fun x => congrFun hpost x

/-- The word-view replay carrier of 3Crv over the collision universe `U`. -/
def viewCarrier (ca : Adr) (U : Key → Prop) : ReplayCarrier ca where
  readsStorage := true
  Snap := View
  Step := WriterInvocation
  Tag := Unit
  Replay := ViewReplay U
  ofState state := viewOf (state.getStor ca)
  frameEntry _ state := viewOf (state.getStor ca)
  nil := viewReplay_nil U
  silent := fun storage _ => by rw [storage rfl]
  credit := by
    intro _ _ _ _ storage _ _
    exact ⟨[], by rw [storage]; exact viewReplay_nil U _⟩
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
def viewObservation (ca : Adr) (U : Key → Prop) : ReplayObservation (viewCarrier ca U) where
  O := WriterInvocation
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := viewFrameObs ca
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change ViewReplay U (viewOf (pre.getStor ca)) [] (viewOf (post.getStor ca))
    rw [storage]
    exact viewReplay_nil U _

/-! ## The target obligations -/

/-- 3Crv frames spawn only by `STATICCALL`. -/
theorem c3crv_spawnKinds (ca : Adr) : SpawnKinds ca c3crvSem := by
  intro sevm pre post _ hrun _ fork _ node chain x instruction
  exact .inr (parentPrefix_exec_staticcall_of_cert cert_check c3crv_cert_staticOnly
    (root := ⟨0, sevm, pre, .ok post, _⟩) rfl hrun fork chain instruction)

/-- Every committed frame of a static run is static. -/
theorem committedFrames_isStatic {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hs : sevm.isStatic = true) :
    ∀ D ∈ Exec.committedFrames run, D.sevm.isStatic = true := by
  intro D member
  unfold Exec.committedFrames at member
  split at member
  · rcases List.mem_cons.mp member with rfl | hd
    · exact hs
    · exact Exec.descendantFrames_isStatic run hs D hd
  · exact absurd member (List.not_mem_nil)

/-- **The whole-frame obligation**: a committed non-static 3Crv frame replays, from its entry view
to its post view, with exactly the observation of its committed subtree, which is its own
invocation. -/
theorem c3crv_wholeFrame (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    Exec.CoreAccounting.WholeFrameReplay ca c3crvSem (carriedFrameEntry U) (viewCarrier ca U)
      (viewObservation ca U) := by
  intro sevm pre post run committed hcode target fork installed admitted _ nonstatic
  obtain ⟨⟨hstack, hmem⟩, hcd, touched⟩ := admitted.root target
  have descendants : (Exec.descendantFrames run).flatMap (viewFrameObs ca) = [] :=
    Exec.staticOnly_descendantFrames_flatMap_eq_nil ca c3crvSem (carriedFrameEntry U)
      (viewFrameObs ca) ⟨0, sevm, pre, .ok post, run⟩ target installed.1 fork
      (fun chain instruction =>
        parentPrefix_exec_staticcall_of_cert cert_check c3crv_cert_staticOnly
          (root := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode fork chain instruction)
      (fun child _ _ _ _ _ static => List.flatMap_eq_nil_iff.mpr fun D member =>
        viewFrameObs_static (committedFrames_isStatic child static D member))
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
    have replay : CurveReplay U (Devm.getStor pre sevm.currentTarget) invs
        (Devm.getStor post sevm.currentTarget) := by
      refine ⟨?_, fun s K included invariant => ?_⟩
      · intro k hk
        rw [invocationKeys_singleton] at hk
        exact touched k hk
      · have fresh := FreshKeys.of_universe injective apart included touched
        obtain ⟨ow, owner, out, accepted, invariant', _⟩ :=
          (c3crv_frame_refines_raw hcode fork hcd hstack hmem invariant fresh run).1 writer
        obtain ⟨accepted', canonical⟩ := step_ownerWordOf accepted
        refine ⟨out.1, ⟨out, ⟨accepted', fun w h => owner w (canonical w h)⟩, rfl⟩, ?_⟩
        simpa only [invs, invocationKeys_singleton] using invariant'
    exact ⟨invs, viewReplay_of replay, (whole.trans (if_pos writer)).symm⟩
  · have replay : CurveReplay U (Devm.getStor pre sevm.currentTarget) []
        (Devm.getStor post sevm.currentTarget) := by
      refine ⟨by simp only [invocationKeys, List.flatMap_nil, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true], fun s K included invariant => ⟨s, rfl, ?_⟩⟩
      simp only [invocationKeys, List.flatMap_nil, Key.extend_nil]
      have fresh := FreshKeys.of_universe injective apart included touched
      have refinement := c3crv_frame_refines_raw hcode fork hcd hstack hmem invariant fresh run
      exact invariant.of_get_eq fun x => by
        rw [(refinement.2 writer).1 sevm.currentTarget]
    exact ⟨[], viewReplay_of replay, (whole.trans (if_neg writer)).symm⟩

/-- **3Crv's positional ladder** (whole-frame: non-static 3Crv frames are opaque). -/
noncomputable def c3crvPositionalLadder (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    PositionalLadder (curveSpec U) ca (carriedFrameEntry U) :=
  wholeFramePositionalLadder (viewCarrier ca U) (viewObservation ca U) viewReplay_append
    (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => Subtype.ext (funext h)) (fun _ hf => viewFrameObs_static hf)
    (fun _ hf => viewFrameObs_foreign hf) (c3crv_spawnKinds ca) (c3crv_wholeFrame ca U injective apart)
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
    (c3crvPositionalLadder ca U topology.inj topology.apart).configuredHistory_at trace admitted
      start before f after split noOpaque
  change ViewReplay U (viewOf (checkpoint.state.getStor ca)) steps
    (viewOf (f.pre.state.getStor ca)) at replay
  change steps = before.flatMap (viewFrameObs ca) at observed
  subst observed
  obtain ⟨s, run, final⟩ := (replay _ _ rfl rfl).2 initial initialKeys (fun _ hk => Or.inl hk)
    invariant
  exact ⟨s, run, final⟩

end Blanc.Composition.Curve3CrvToken
