import Blanc.Lift.Curve3Crv.CommittedHistory

/-!
# The Curve committed replay, keeping each frame's own storage boundaries

`CurveReplayBy` (`CommittedReplay.lean`) relates the storage at the two ends of a span to the model
run over its committed writer invocations. `CurveFrameReplayBy` also keeps, for every invocation of
the span, the frame's own opening and closing storage as abstractions of the model step it runs
(`FrameModelBy`), so frame-level facts about storage words (the policy headline, `Headline.lean`)
can be read off the model step. The historical ladder (`HistCommittedHistory.lean`) carries this
stronger relation; `CurveReplayBy` is its first part (`CurveFrameReplayBy.toCurveReplayBy`).
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionAccountingReplay Blanc.ExecutionTrace


/-- **One committed writer frame read through the model**: the frame's opening storage at `ca`
abstracts some model state `s` over live keys `K` (inside the universe `U`, and containing every key
the frame's call touches), the model accepts the frame's call from `s` with the frame's owner
evidence, and the frame's closing storage abstracts the step's result over the same keys. -/
def FrameModelBy (A : Sevm → Devm → Adr → B256 → Prop) (ca : Adr) (U : Key → Prop)
    (inv : WriterInvocation) : Prop :=
  ∃ s o K, ModelStepBy A inv s o ∧ (∀ k, K k → U k) ∧
    (∀ k ∈ callKeys inv.sevm.caller (decodeCall inv.sevm), K k) ∧
    VyInv (Devm.getStor inv.pre ca) s K ∧ VyInv (Devm.getStor inv.post ca) o.1 K

/-- `CurveReplayBy`, keeping every invocation's own storage boundaries (`FrameModelBy`). -/
def CurveFrameReplayBy (A : Sevm → Devm → Adr → B256 → Prop) (ca : Adr) (U : Key → Prop)
    (pre : Stor) (invs : List WriterInvocation) (post : Stor) : Prop :=
  (∀ k ∈ invocationKeys invs, U k) ∧
    ∀ s K, (∀ k, K k → U k) → VyInv pre s K →
      ∃ s', InvRunBy A s invs s' ∧ (∀ inv ∈ invs, FrameModelBy A ca U inv) ∧
        VyInv post s' (Key.extend K (invocationKeys invs))

theorem CurveFrameReplayBy.toCurveReplayBy {A : Sevm → Devm → Adr → B256 → Prop} {ca : Adr}
    {U : Key → Prop} {pre post : Stor} {invs : List WriterInvocation}
    (h : CurveFrameReplayBy A ca U pre invs post) : CurveReplayBy A U pre invs post :=
  ⟨h.1, fun s K hK hinv => by
    obtain ⟨s', run, -, final⟩ := h.2 s K hK hinv
    exact ⟨s', run, final⟩⟩

theorem CurveFrameReplayBy.nil (A : Sevm → Devm → Adr → B256 → Prop) (ca : Adr)
    (U : Key → Prop) (stor : Stor) : CurveFrameReplayBy A ca U stor [] stor := by
  refine ⟨(CurveReplayBy.nil A U stor).1, fun s K _ h =>
    ⟨s, rfl, (fun _ h => by cases h), ?_⟩⟩
  simpa only [invocationKeys, List.flatMap_nil, Key.extend_nil] using h

theorem CurveFrameReplayBy.append {A : Sevm → Devm → Adr → B256 → Prop} {ca : Adr}
    {U : Key → Prop} {a b c : Stor} {xs ys : List WriterInvocation}
    (first : CurveFrameReplayBy A ca U a xs b) (second : CurveFrameReplayBy A ca U b ys c) :
    CurveFrameReplayBy A ca U a (xs ++ ys) c := by
  refine ⟨(first.toCurveReplayBy.append second.toCurveReplayBy).1, fun s K hK h => ?_⟩
  obtain ⟨s₁, run₁, frames₁, inv₁⟩ := first.2 s K hK h
  have hK₁ : ∀ k, Key.extend K (invocationKeys xs) k → U k := by
    intro k hk
    exact hk.elim (hK k) (first.1 k)
  obtain ⟨s₂, run₂, frames₂, inv₂⟩ := second.2 s₁ _ hK₁ inv₁
  refine ⟨s₂, run₁.append run₂, fun inv member => ?_, ?_⟩
  · rcases List.mem_append.mp member with member | member
    · exact frames₁ inv member
    · exact frames₂ inv member
  · simpa only [Key.extend_append, invocationKeys, List.flatMap_append] using inv₂

/-- One writer frame's replay from a model step out of an abstraction of its opening storage over
`K` (inside `U`), its call's keys fresh for `K` and inside `U`, and its closing storage abstracting
the step's result over the extended keys. -/
theorem CurveFrameReplayBy.singleton {A : Sevm → Devm → Adr → B256 → Prop} {ca : Adr}
    {U K : Key → Prop} {inv : WriterInvocation} {s : Blanc.Curve3Crv.State}
    {o : Blanc.Curve3Crv.Out} (step : ModelStepBy A inv s o) (included : ∀ k, K k → U k)
    (touched : ∀ k ∈ callKeys inv.sevm.caller (decodeCall inv.sevm), U k)
    (fresh : FreshKeys K (callKeys inv.sevm.caller (decodeCall inv.sevm)))
    (before : VyInv (Devm.getStor inv.pre ca) s K)
    (after : VyInv (Devm.getStor inv.post ca) o.1
      (Key.extend K (callKeys inv.sevm.caller (decodeCall inv.sevm)))) :
    ∃ s', InvRunBy A s [inv] s' ∧ (∀ i ∈ [inv], FrameModelBy A ca U i) ∧
      VyInv (Devm.getStor inv.post ca) s' (Key.extend K (invocationKeys [inv])) := by
  refine ⟨o.1, ⟨o, step, rfl⟩, fun i member => ?_, ?_⟩
  · rw [List.mem_singleton] at member
    subst member
    exact ⟨s, o, _, step, fun k hk => hk.elim (included k) (touched k), fun k hk => Or.inr hk,
      before.extend fresh, after⟩
  · simpa only [invocationKeys_singleton] using after

/-- The storage-only replay carrier keeping each frame's boundaries (`curveCarrierBy` with
`CurveFrameReplayBy`). -/
def curveFrameCarrierBy (A : Sevm → Devm → Adr → B256 → Prop) (ca : Adr) (U : Key → Prop) :
    ReplayCarrier ca where
  readsStorage := true
  Snap := Stor
  Step := WriterInvocation
  Tag := Unit
  Replay := CurveFrameReplayBy A ca U
  ofState state := state.getStor ca
  frameEntry _ state := state.getStor ca
  nil := CurveFrameReplayBy.nil A ca U
  silent := fun storage _ => storage rfl
  credit := by
    intro _ _ _ _ storage _ _
    exact ⟨[], by rw [storage]; exact CurveFrameReplayBy.nil A ca U _⟩
  entry_eq_ofState := (curveCarrierBy A ca U).entry_eq_ofState

/-- The ordered observation of `curveFrameCarrierBy`: its steps are the committed invocations. -/
def curveFrameObservationBy (A : Sevm → Devm → Adr → B256 → Prop) (ca : Adr) (U : Key → Prop) :
    ReplayObservation (curveFrameCarrierBy A ca U) where
  O := WriterInvocation
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := committedFrameInvocations ca
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change CurveFrameReplayBy A ca U (pre.getStor ca) [] (post.getStor ca)
    rw [storage]
    exact CurveFrameReplayBy.nil A ca U _

end Blanc.Lift.Curve3Crv
