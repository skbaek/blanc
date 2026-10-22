import Blanc.ExecutionStagedFrames
import Blanc.ExecutionTraceEntered

/-!
Entry-only admission over the raw interpreter roots of supplied staged bodies
and selected-domain histories. Frame-free passes and skipped stages add no
interpreter obligation. These predicates impose no outcome or invariant law.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Admission only for the actual message retained by an enabled beacon stage. -/
def BeaconStageTrace.FrameAdmitted
    (trace : BeaconStageTrace rules benv state bal)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .skipped .. => True
  | .called _ _ message _ _ => message.FrameAdmitted ca entry

/-- Disabled history storage has no message whose interpreter roots need admission. -/
def HistoryStageTrace.FrameAdmitted
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .skipped .. => True
  | .called _ _ _ _ message _ _ => message.FrameAdmitted ca entry

/-- An enabled request stage inherits the supplied two-call admission. -/
def RequestStageTrace.FrameAdmitted
    (trace : RequestStageTrace rules benv bout state bout')
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .skipped .. => True
  | .called _ requests _ => requests.FrameAdmitted ca entry

/-- Admission for the supplied interpreter-bearing body components only. -/
structure StagedBodyTrace.FrameAdmitted
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop where
  beacon : trace.beacon.FrameAdmitted ca entry
  history : trace.history.FrameAdmitted ca entry
  transactions : trace.transactions.FrameAdmitted ca entry
  requests : trace.requests.FrameAdmitted ca entry

/-- A selected-domain block inherits its actual supplied body's admission. -/
def ConfiguredBlockTraceIn.FrameAdmitted
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  trace.bodyTrace.FrameAdmitted ca entry

/-- Pointwise admission on the supplied selected-domain block spine. -/
def ConfiguredHistoryTraceIn.FrameAdmitted
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .refl .. => True
  | .step prior block => prior.FrameAdmitted ca entry ∧ block.FrameAdmitted ca entry

/-- Beacon admission is exactly the entry condition at every actual raw root. -/
theorem BeaconStageTrace.frameAdmitted_iff_rawFrames
    (trace : BeaconStageTrace rules benv state bal)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  cases trace with
  | skipped =>
      simp only [BeaconStageTrace.FrameAdmitted, BeaconStageTrace.rawFrames,
        List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | called enabled out message incorporated run =>
      exact message.frameAdmitted_iff_rawFrames ca entry

/-- History admission includes every raw root of its supplied message. -/
theorem HistoryStageTrace.frameAdmitted_iff_rawFrames
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  cases trace with
  | skipped =>
      simp only [HistoryStageTrace.FrameAdmitted, HistoryStageTrace.rawFrames,
        List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | called enabled lastHash lastHashRun out message incorporated run =>
      exact message.frameAdmitted_iff_rawFrames ca entry

/-- Request admission uses its real ordered raw invocations, before settlement filtering. -/
theorem RequestStageTrace.frameAdmitted_iff_rawFrames
    (trace : RequestStageTrace rules benv bout state bout')
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  cases trace with
  | skipped =>
      simp only [RequestStageTrace.FrameAdmitted, RequestStageTrace.rawFrames,
        List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | called enabled requests run =>
      exact requests.frameAdmitted_iff_rawFrames ca entry

/-- Staged admission is exactly raw-entry admission in body order. -/
theorem StagedBodyTrace.frameAdmitted_iff_rawFrames
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  have parts : trace.FrameAdmitted ca entry ↔
      ((trace.beacon.FrameAdmitted ca entry ∧ trace.history.FrameAdmitted ca entry) ∧
        trace.transactions.FrameAdmitted ca entry) ∧ trace.requests.FrameAdmitted ca entry :=
    ⟨fun h => ⟨⟨⟨h.beacon, h.history⟩, h.transactions⟩, h.requests⟩,
      fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [parts]
  simp only [StagedBodyTrace.rawFrames, BeaconStageTrace.frameAdmitted_iff_rawFrames,
    HistoryStageTrace.frameAdmitted_iff_rawFrames,
    ApplyTransactionsTrace.frameAdmitted_iff_rawFrames,
    RequestStageTrace.frameAdmitted_iff_rawFrames, List.mem_append, or_imp, forall_and]

/-- Block admission imposes exactly its retained body's raw-root obligations. -/
theorem ConfiguredBlockTraceIn.frameAdmitted_iff_rawFrames
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm :=
  trace.bodyTrace.frameAdmitted_iff_rawFrames ca entry

/-- History admission quantifies every raw entry in the supplied spine. -/
theorem ConfiguredHistoryTraceIn.frameAdmitted_iff_rawFrames
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  induction trace with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.FrameAdmitted, ConfiguredHistoryTraceIn.rawFrames,
        List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.FrameAdmitted, ConfiguredHistoryTraceIn.rawFrames,
        ih, block.frameAdmitted_iff_rawFrames ca entry, List.mem_append, or_imp, forall_and]

/-- Every actual beacon root satisfies a condition supplied by genuine frame entry. -/
theorem BeaconStageTrace.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : BeaconStageTrace rules benv state bal) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  cases trace with
  | skipped => intro root member; exact False.elim (List.not_mem_nil member)
  | called enabled out message incorporated run => exact message.rawFrames_entered hE

/-- The optional history stage retains only genuinely entered raw roots. -/
theorem HistoryStageTrace.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : HistoryStageTrace rules benv inputBal state bal) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  cases trace with
  | skipped => intro root member; exact False.elim (List.not_mem_nil member)
  | called enabled lastHash lastHashRun out message incorporated run =>
      exact message.rawFrames_entered hE

/-- Both actual request calls inherit the existing frame-entry guarantee. -/
theorem RequestStageTrace.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : RequestStageTrace rules benv bout state bout') :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  cases trace with
  | skipped => intro root member; exact False.elim (List.not_mem_nil member)
  | called enabled requests run => exact requests.rawFrames_entered hE

/-- All interpreter-bearing stages retain the actual entry condition. -/
theorem StagedBodyTrace.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : StagedBodyTrace benv txs ommers wds state bout) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  intro root member
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((beacon | history) | transactions) | requests
  · exact trace.beacon.rawFrames_entered hE root beacon
  · exact trace.history.rawFrames_entered hE root history
  · exact trace.transactions.rawFrames_entered hE root transactions
  · exact trace.requests.rawFrames_entered hE root requests

/-- A selected-domain block uses its supplied body's actual raw entries. -/
theorem ConfiguredBlockTraceIn.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : ConfiguredBlockTraceIn F cfg pre post) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm :=
  trace.bodyTrace.rawFrames_entered hE

/-- The supplied selected-domain spine retains the guarantee at every raw entry. -/
theorem ConfiguredHistoryTraceIn.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  induction trace with
  | refl => intro root member; exact False.elim (List.not_mem_nil member)
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at member
      rcases member with priorMember | blockMember
      · exact ih root priorMember
      · exact block.rawFrames_entered hE root blockMember

/-- Genuine entry conditions give admission at every selected target. -/
theorem BeaconStageTrace.frameAdmitted_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : BeaconStageTrace rules benv state bal) (ca : Adr) :
    trace.FrameAdmitted ca E := by
  rw [BeaconStageTrace.frameAdmitted_iff_rawFrames]
  intro root member _
  exact trace.rawFrames_entered hE root member

/-- Genuine entry conditions give admission at every selected target. -/
theorem HistoryStageTrace.frameAdmitted_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : HistoryStageTrace rules benv inputBal state bal) (ca : Adr) :
    trace.FrameAdmitted ca E := by
  rw [HistoryStageTrace.frameAdmitted_iff_rawFrames]
  intro root member _
  exact trace.rawFrames_entered hE root member

/-- Genuine entry conditions give admission at every selected target. -/
theorem RequestStageTrace.frameAdmitted_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : RequestStageTrace rules benv bout state bout') (ca : Adr) :
    trace.FrameAdmitted ca E := by
  rw [RequestStageTrace.frameAdmitted_iff_rawFrames]
  intro root member _
  exact trace.rawFrames_entered hE root member

/-- Genuine entry conditions give admission at every selected target. -/
theorem StagedBodyTrace.frameAdmitted_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : StagedBodyTrace benv txs ommers wds state bout) (ca : Adr) :
    trace.FrameAdmitted ca E := by
  rw [StagedBodyTrace.frameAdmitted_iff_rawFrames]
  intro root member _
  exact trace.rawFrames_entered hE root member

/-- Genuine entry conditions give admission at every selected target. -/
theorem ConfiguredBlockTraceIn.frameAdmitted_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : ConfiguredBlockTraceIn F cfg pre post) (ca : Adr) :
    trace.FrameAdmitted ca E := by
  rw [ConfiguredBlockTraceIn.frameAdmitted_iff_rawFrames]
  intro root member _
  exact trace.rawFrames_entered hE root member

/-- Genuine entry conditions give admission at every selected target. -/
theorem ConfiguredHistoryTraceIn.frameAdmitted_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (ca : Adr) :
    trace.FrameAdmitted ca E := by
  rw [ConfiguredHistoryTraceIn.frameAdmitted_iff_rawFrames]
  intro root member _
  exact trace.rawFrames_entered hE root member

/-- Every retained raw frame enters with empty stack and memory. -/
theorem BeaconStageTrace.freshFrameAdmitted
    (trace : BeaconStageTrace rules benv state bal) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.frameAdmitted_entered enteredCondition_fresh ca

/-- Every retained raw frame enters with empty stack and memory. -/
theorem HistoryStageTrace.freshFrameAdmitted
    (trace : HistoryStageTrace rules benv inputBal state bal) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.frameAdmitted_entered enteredCondition_fresh ca

/-- Every retained raw frame enters with empty stack and memory. -/
theorem RequestStageTrace.freshFrameAdmitted
    (trace : RequestStageTrace rules benv bout state bout') (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.frameAdmitted_entered enteredCondition_fresh ca

/-- Every retained raw frame enters with empty stack and memory. -/
theorem StagedBodyTrace.freshFrameAdmitted
    (trace : StagedBodyTrace benv txs ommers wds state bout) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.frameAdmitted_entered enteredCondition_fresh ca

/-- Every retained raw frame enters with empty stack and memory. -/
theorem ConfiguredBlockTraceIn.freshFrameAdmitted
    (trace : ConfiguredBlockTraceIn F cfg pre post) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.frameAdmitted_entered enteredCondition_fresh ca

/-- Every retained raw frame enters with empty stack and memory. -/
theorem ConfiguredHistoryTraceIn.freshFrameAdmitted
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.frameAdmitted_entered enteredCondition_fresh ca

/-- Admission composes pointwise on the same retained raw entries. -/
theorem BeaconStageTrace.FrameAdmitted.and
    {trace : BeaconStageTrace rules benv state bal} {ca : Adr}
    {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left) (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  rw [BeaconStageTrace.frameAdmitted_iff_rawFrames] at hleft hright ⊢
  intro root member target
  exact ⟨hleft root member target, hright root member target⟩

/-- Admission composes pointwise on the same retained raw entries. -/
theorem HistoryStageTrace.FrameAdmitted.and
    {trace : HistoryStageTrace rules benv inputBal state bal} {ca : Adr}
    {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left) (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  rw [HistoryStageTrace.frameAdmitted_iff_rawFrames] at hleft hright ⊢
  intro root member target
  exact ⟨hleft root member target, hright root member target⟩

/-- Admission composes pointwise on the same retained raw entries. -/
theorem RequestStageTrace.FrameAdmitted.and
    {trace : RequestStageTrace rules benv bout state bout'} {ca : Adr}
    {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left) (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  rw [RequestStageTrace.frameAdmitted_iff_rawFrames] at hleft hright ⊢
  intro root member target
  exact ⟨hleft root member target, hright root member target⟩

/-- Admission composes pointwise on the same retained raw entries. -/
theorem StagedBodyTrace.FrameAdmitted.and
    {trace : StagedBodyTrace benv txs ommers wds state bout} {ca : Adr}
    {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left) (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  rw [StagedBodyTrace.frameAdmitted_iff_rawFrames] at hleft hright ⊢
  intro root member target
  exact ⟨hleft root member target, hright root member target⟩

/-- Admission composes pointwise on the same retained raw entries. -/
theorem ConfiguredBlockTraceIn.FrameAdmitted.and
    {trace : ConfiguredBlockTraceIn F cfg pre post} {ca : Adr}
    {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left) (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  rw [ConfiguredBlockTraceIn.frameAdmitted_iff_rawFrames] at hleft hright ⊢
  intro root member target
  exact ⟨hleft root member target, hright root member target⟩

/-- Admission composes pointwise on the same retained raw entries. -/
theorem ConfiguredHistoryTraceIn.FrameAdmitted.and
    {trace : ConfiguredHistoryTraceIn F cfg checkpoint future} {ca : Adr}
    {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left) (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  rw [ConfiguredHistoryTraceIn.frameAdmitted_iff_rawFrames] at hleft hright ⊢
  intro root member target
  exact ⟨hleft root member target, hright root member target⟩

end Blanc.ExecutionTrace
