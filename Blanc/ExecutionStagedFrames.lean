import Blanc.ExecutionTraceSettledOrigin

/-!
Raw and full-settlement frame enumeration for supplied optional body stages
and selected-domain configured traces. Disabled stages retain no invocation.
The traversal keeps supplied execution evidence and chronological list order;
it assigns no contract meaning to the enumerated frames.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- All actually entered roots of an optional beacon stage. -/
def BeaconStageTrace.rawFrames
    (trace : BeaconStageTrace rules benv state bal) : List Exec.Deriv :=
  match trace with
  | .skipped .. => []
  | .called _ _ message _ _ => message.rawFrames

/-- Beacon roots surviving full message settlement. -/
def BeaconStageTrace.settledFrames
    (trace : BeaconStageTrace rules benv state bal) : List Exec.Frame :=
  match trace with
  | .skipped .. => []
  | .called _ _ message _ _ => message.settledFrames

/-- All actually entered roots of an optional history stage. -/
def HistoryStageTrace.rawFrames
    (trace : HistoryStageTrace rules benv inputBal state bal) : List Exec.Deriv :=
  match trace with
  | .skipped .. => []
  | .called _ _ _ _ message _ _ => message.rawFrames

/-- History roots surviving full message settlement. -/
def HistoryStageTrace.settledFrames
    (trace : HistoryStageTrace rules benv inputBal state bal) : List Exec.Frame :=
  match trace with
  | .skipped .. => []
  | .called _ _ _ _ message _ _ => message.settledFrames

/-- Actual request roots, withdrawal before consolidation when enabled. -/
def RequestStageTrace.rawFrames
    (trace : RequestStageTrace rules benv bout state bout') : List Exec.Deriv :=
  match trace with
  | .skipped .. => []
  | .called _ requests _ => requests.rawFrames

/-- Request roots surviving full message settlement, in the same order. -/
def RequestStageTrace.settledFrames
    (trace : RequestStageTrace rules benv bout state bout') : List Exec.Frame :=
  match trace with
  | .skipped .. => []
  | .called _ requests _ => requests.settledFrames

/-- Raw body roots; withdrawals, rewards and BAL finishing are frame-free. -/
def StagedBodyTrace.rawFrames
    (trace : StagedBodyTrace benv txs ommers wds state bout) : List Exec.Deriv :=
  trace.beacon.rawFrames ++ trace.history.rawFrames ++
    trace.transactions.rawFrames ++ trace.requests.rawFrames

/-- Full-settlement body roots in beacon/history/transaction/request order. -/
def StagedBodyTrace.settledFrames
    (trace : StagedBodyTrace benv txs ommers wds state bout) : List Exec.Frame :=
  trace.beacon.settledFrames ++ trace.history.settledFrames ++
    trace.transactions.settledFrames ++ trace.requests.settledFrames

/-- Project the supplied body without a new condition on the selected domain. -/
def ConfiguredBlockTraceIn.rawFrames
    (trace : ConfiguredBlockTraceIn F cfg pre post) : List Exec.Deriv :=
  trace.bodyTrace.rawFrames

/-- Full-settlement roots of the supplied selected-domain block. -/
def ConfiguredBlockTraceIn.settledFrames
    (trace : ConfiguredBlockTraceIn F cfg pre post) : List Exec.Frame :=
  trace.bodyTrace.settledFrames

/-- Raw roots of successive blocks, retaining each block's selected fork. -/
def ConfiguredHistoryTraceIn.rawFrames :
    ConfiguredHistoryTraceIn F cfg checkpoint future → List Exec.Deriv
  | .refl .. => []
  | .step prior block => prior.rawFrames ++ block.rawFrames

/-- Full-settlement roots of successive blocks in supplied spine order. -/
def ConfiguredHistoryTraceIn.settledFrames :
    ConfiguredHistoryTraceIn F cfg checkpoint future → List Exec.Frame
  | .refl .. => []
  | .step prior block => prior.settledFrames ++ block.settledFrames

/-- A disabled stage enumerates no raw frame roots. -/
theorem BeaconStageTrace.rawFrames_of_disabled
    (trace : BeaconStageTrace rules benv state bal)
    (disabled : rules.sys.beaconRoots = false) : trace.rawFrames = [] := by
  cases trace <;> simp_all only [BeaconStageTrace.rawFrames, Bool.true_eq_false]

/-- A disabled stage enumerates no settlement-retained frame roots. -/
theorem BeaconStageTrace.settledFrames_of_disabled
    (trace : BeaconStageTrace rules benv state bal)
    (disabled : rules.sys.beaconRoots = false) : trace.settledFrames = [] := by
  cases trace <;> simp_all only [BeaconStageTrace.settledFrames, Bool.true_eq_false]

/-- A disabled stage enumerates no raw frame roots. -/
theorem HistoryStageTrace.rawFrames_of_disabled
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (disabled : rules.sys.historyStorage = false) : trace.rawFrames = [] := by
  cases trace <;> simp_all only [HistoryStageTrace.rawFrames, Bool.true_eq_false]

/-- A disabled stage enumerates no settlement-retained frame roots. -/
theorem HistoryStageTrace.settledFrames_of_disabled
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (disabled : rules.sys.historyStorage = false) : trace.settledFrames = [] := by
  cases trace <;> simp_all only [HistoryStageTrace.settledFrames, Bool.true_eq_false]

/-- A disabled stage enumerates no raw frame roots. -/
theorem RequestStageTrace.rawFrames_of_disabled
    (trace : RequestStageTrace rules benv bout state bout')
    (disabled : rules.header.requestsHash = false) : trace.rawFrames = [] := by
  cases trace <;> simp_all only [RequestStageTrace.rawFrames, Bool.true_eq_false]

/-- A disabled stage enumerates no settlement-retained frame roots. -/
theorem RequestStageTrace.settledFrames_of_disabled
    (trace : RequestStageTrace rules benv bout state bout')
    (disabled : rules.header.requestsHash = false) : trace.settledFrames = [] := by
  cases trace <;> simp_all only [RequestStageTrace.settledFrames, Bool.true_eq_false]

/-- Every retained beacon frame came from an actual raw invocation. -/
theorem BeaconStageTrace.mem_rawFrames_of_mem_settledFrames
    (trace : BeaconStageTrace rules benv state bal) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  cases trace with
  | skipped => exact False.elim (List.not_mem_nil member)
  | called enabled out message incorporated run =>
      exact message.mem_rawFrames_of_mem_settledFrames frame member

/-- Retained history frames preserve their actual invocation roots. -/
theorem HistoryStageTrace.mem_rawFrames_of_mem_settledFrames
    (trace : HistoryStageTrace rules benv inputBal state bal) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  cases trace with
  | skipped => exact False.elim (List.not_mem_nil member)
  | called enabled lastHash lastHashRun out message incorporated run =>
      exact message.mem_rawFrames_of_mem_settledFrames frame member

/-- Both retained request calls came from the supplied ordered raw requests. -/
theorem RequestStageTrace.mem_rawFrames_of_mem_settledFrames
    (trace : RequestStageTrace rules benv bout state bout') (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  cases trace with
  | skipped => exact False.elim (List.not_mem_nil member)
  | called enabled requests run =>
      simp only [RequestStageTrace.settledFrames, RequestsTrace.settledFrames,
        List.mem_append] at member
      simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append]
      rcases member with withdrawal | consolidation
      · exact Or.inl (requests.withdrawal.mem_rawFrames_of_mem_settledFrames frame withdrawal)
      · exact Or.inr (requests.consolidation.mem_rawFrames_of_mem_settledFrames frame consolidation)

/-- Settlement retains only roots from the supplied raw body traversal. -/
theorem StagedBodyTrace.mem_rawFrames_of_mem_settledFrames
    (trace : StagedBodyTrace benv txs ommers wds state bout) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  simp only [StagedBodyTrace.settledFrames, List.mem_append] at member
  simp only [StagedBodyTrace.rawFrames, List.mem_append]
  rcases member with ((beacon | history) | transactions) | requests
  · exact Or.inl (Or.inl (Or.inl
      (trace.beacon.mem_rawFrames_of_mem_settledFrames frame beacon)))
  · exact Or.inl (Or.inl (Or.inr
      (trace.history.mem_rawFrames_of_mem_settledFrames frame history)))
  · exact Or.inl (Or.inr
      (trace.transactions.mem_rawFrames_of_mem_settledFrames frame transactions))
  · exact Or.inr (trace.requests.mem_rawFrames_of_mem_settledFrames frame requests)

/-- A selected-domain block retains only its supplied raw body roots. -/
theorem ConfiguredBlockTraceIn.mem_rawFrames_of_mem_settledFrames
    (trace : ConfiguredBlockTraceIn F cfg pre post) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames :=
  trace.bodyTrace.mem_rawFrames_of_mem_settledFrames frame member

/-- The retained history filter never invents a raw invocation root. -/
theorem ConfiguredHistoryTraceIn.mem_rawFrames_of_mem_settledFrames
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  induction trace with
  | refl => exact False.elim (List.not_mem_nil member)
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.settledFrames, List.mem_append] at member
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
      rcases member with priorMember | blockMember
      · exact Or.inl (ih priorMember)
      · exact Or.inr (block.mem_rawFrames_of_mem_settledFrames frame blockMember)

/-- Modern embedding retains the supplied body's raw roots. -/
theorem AppliedBodyTrace.toStaged_rawFrames
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (covered : CoveredFork benv.stat.fork) :
    (trace.toStaged covered).rawFrames = trace.rawFrames := by
  rfl

/-- Modern embedding retains the supplied body's settlement-retained roots. -/
theorem AppliedBodyTrace.toStaged_settledFrames
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (covered : CoveredFork benv.stat.fork) :
    (trace.toStaged covered).settledFrames = trace.settledFrames := by
  rfl

/-- Domain embedding enumerates the same raw block roots. -/
theorem ConfiguredBlockTrace.toIn_rawFrames
    (trace : ConfiguredBlockTrace cfg pre post) :
    trace.toIn.rawFrames = trace.rawFrames := by
  change (trace.bodyTrace.toStaged trace.covered).rawFrames = trace.bodyTrace.rawFrames
  exact trace.bodyTrace.toStaged_rawFrames trace.covered

/-- Domain embedding enumerates the same settlement-retained block roots. -/
theorem ConfiguredBlockTrace.toIn_settledFrames
    (trace : ConfiguredBlockTrace cfg pre post) :
    trace.toIn.settledFrames = trace.settledFrames := by
  change (trace.bodyTrace.toStaged trace.covered).settledFrames = trace.bodyTrace.settledFrames
  exact trace.bodyTrace.toStaged_settledFrames trace.covered

/-- Modern history embedding preserves the supplied raw spine order. -/
theorem ConfiguredHistoryTrace.toIn_rawFrames
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    trace.toIn.rawFrames = trace.rawFrames := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTrace.toIn, ConfiguredHistoryTraceIn.rawFrames,
        ConfiguredHistoryTrace.rawFrames, ih, ConfiguredBlockTrace.toIn_rawFrames]

/-- Modern history embedding preserves the supplied settlement-retained spine order. -/
theorem ConfiguredHistoryTrace.toIn_settledFrames
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    trace.toIn.settledFrames = trace.settledFrames := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTrace.toIn, ConfiguredHistoryTraceIn.settledFrames,
        ConfiguredHistoryTrace.settledFrames, ih, ConfiguredBlockTrace.toIn_settledFrames]

/-- Align only the supplied stage endpoints before transporting their frame
projections. Reward/BAL normalization and whole-carrier equality are irrelevant. -/
private theorem StagedBodyTrace.frameProjections_eq_of_components
    (left right : StagedBodyTrace benv txs ommers wds state bout)
    (beacon : HEq left.beacon right.beacon)
    (history : HEq left.history right.history)
    (transactions : HEq left.transactions right.transactions)
    (requests : HEq left.requests right.requests) :
    left.rawFrames = right.rawFrames ∧ left.settledFrames = right.settledFrames := by
  rcases left with ⟨lrun, lbs, lbb, lb, lhs, lhb, lh, ldecoded, ldecode,
    lbenv, lbout, ltxs, ltrun, lws, lwbout, lwrun, lrs, lrbout, lr,
    lrwd, lrwdeq, lsteq, llist, llisteq, lgas, lbouteq⟩
  rcases right with ⟨rrun, rbs, rbb, rb, rhs, rhb, rh, rdecoded, rdecode,
    rbenv, rbout, rtxs, rtrun, rws, rwbout, rwrun, rrs, rrbout, rr,
    rrwd, rrwdeq, rsteq, rlist, rlisteq, rgas, rbouteq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (lb.result.symm.trans rb.result))
  cases (eq_of_heq beacon)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (lh.result.symm.trans rh.result))
  cases (eq_of_heq history)
  cases (Except.ok.inj (ldecode.symm.trans rdecode))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (ltrun.symm.trans rtrun))
  cases (eq_of_heq transactions)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (lwrun.symm.trans rwrun)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (lr.result.symm.trans rr.result))
  cases (eq_of_heq requests)
  exact ⟨rfl, rfl⟩

/-- Recovering modern data preserves the supplied raw body roots. -/
theorem StagedBodyTrace.toModern_rawFrames
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (covered : CoveredFork benv.stat.fork) :
    (trace.toModern covered).rawFrames = trace.rawFrames := by
  obtain ⟨beacon, history, transactions, requests⟩ := trace.toModern_preserves covered
  have frames := StagedBodyTrace.frameProjections_eq_of_components
    ((trace.toModern covered).toStaged covered) trace beacon history transactions requests
  exact ((trace.toModern covered).toStaged_rawFrames covered).symm.trans frames.1

/-- Recovering modern data preserves the same full-settlement body roots. -/
theorem StagedBodyTrace.toModern_settledFrames
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (covered : CoveredFork benv.stat.fork) :
    (trace.toModern covered).settledFrames = trace.settledFrames := by
  obtain ⟨beacon, history, transactions, requests⟩ := trace.toModern_preserves covered
  have frames := StagedBodyTrace.frameProjections_eq_of_components
    ((trace.toModern covered).toStaged covered) trace beacon history transactions requests
  exact ((trace.toModern covered).toStaged_settledFrames covered).symm.trans frames.2

/-- Recovering a covered block preserves its supplied raw roots. -/
theorem ConfiguredBlockTraceIn.toModern_rawFrames
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (covered : CoveredFork trace.fork) :
    (trace.toModern covered).rawFrames = trace.rawFrames := by
  change (trace.bodyTrace.toModern covered).rawFrames = trace.bodyTrace.rawFrames
  exact trace.bodyTrace.toModern_rawFrames covered

/-- Recovering a covered block preserves its supplied settlement-retained roots. -/
theorem ConfiguredBlockTraceIn.toModern_settledFrames
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (covered : CoveredFork trace.fork) :
    (trace.toModern covered).settledFrames = trace.settledFrames := by
  change (trace.bodyTrace.toModern covered).settledFrames = trace.bodyTrace.settledFrames
  exact trace.bodyTrace.toModern_settledFrames covered

/-- Recovering a covered history retains its actual raw spine order. -/
theorem ConfiguredHistoryTraceIn.toModern_rawFrames
    (trace : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    trace.toModern.rawFrames = trace.rawFrames := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.toModern, ConfiguredHistoryTrace.rawFrames,
        ConfiguredHistoryTraceIn.rawFrames, ih, ConfiguredBlockTraceIn.toModern_rawFrames]

/-- Recovering a covered history retains its actual settlement-retained spine order. -/
theorem ConfiguredHistoryTraceIn.toModern_settledFrames
    (trace : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    trace.toModern.settledFrames = trace.settledFrames := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.toModern, ConfiguredHistoryTrace.settledFrames,
        ConfiguredHistoryTraceIn.settledFrames, ih, ConfiguredBlockTraceIn.toModern_settledFrames]

end Blanc.ExecutionTrace
