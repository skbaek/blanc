import Blanc.Lift.SegmentedReplay
import Blanc.ExecutionHistoryStateTrace

/-!
A local segmented consumer of the existing configured-history chronology.
The original wrappers, selected fork witnesses and state boundaries stay in
that chronology; raw frame boundaries are exposed only for cut admissibility.
-/

namespace Blanc

open Jaune

open scoped _root_.List

/-- A projection value, not an execution carrier: retain an original foreign
boundary or one original located target frame whose outer traversal stops here. -/
abbrev Exec.RetainedTargetTurn := Exec.StateBoundary ⊕ Exec.LocatedFrame

/-- Expansion reuses the existing boundary or the target frame's actual
settlement-pruned transcript at its original unrenumbered path. -/
def Exec.RetainedTargetTurn.expand : Exec.RetainedTargetTurn → List Exec.StateBoundary
  | .inl boundary => [boundary]
  | .inr located => Exec.stateBoundariesOfCommits located.path 0
      located.frame.run located.frame.committed

private def Exec.retainedTargetTurnsFrom (ca : Adr) (framePath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List Exec.RetainedTargetTurn :=
  if sevm.currentTarget = ca then
    [.inr ⟨framePath, Exec.Frame.ofRun run committed⟩]
  else
    let driver := Exec.Frame.ofRun run committed
    match run with
    | .halt _ =>
        [.inl (Exec.stateBoundary framePath driver .terminal pre.state
          (Execution.committedPost out committed).state)]
    | .cont _ next =>
        .inl (Exec.stateBoundary framePath driver .instruction pre.state
          (Exec.startState next)) ::
          Exec.retainedTargetTurnsFrom ca framePath nextChild next committed
    | .doneErr _ _ _ => by simp only [Execution.commits, Bool.false_eq_true] at committed
    | .doneOk _ _ _ next =>
        .inl (Exec.stateBoundary framePath driver .childless pre.state
          (Exec.startState next)) ::
          Exec.retainedTargetTurnsFrom ca framePath (nextChild + 1) next committed
    | .runErr _ _ _ _ => by simp only [Execution.commits, Bool.false_eq_true] at committed
    | .runOk (f := frame) (raw := raw) _ _ child _ next =>
        if h : Frame.settlementCommits frame raw = true then
          let childCommitted := Frame.raw_commits_of_settlementCommits h
          .inl (Exec.stateBoundary framePath driver .childEntry pre.state
            (Exec.startState child)) ::
            (Exec.retainedTargetTurnsFrom ca (framePath ++ [nextChild]) 0 child childCommitted ++
              .inl (Exec.stateBoundary framePath driver .childSettlement
                (Execution.committedPost raw childCommitted).state (Exec.startState next)) ::
                Exec.retainedTargetTurnsFrom ca framePath (nextChild + 1) next committed)
        else
          .inl (Exec.stateBoundary framePath driver .childRollback pre.state
            (Exec.startState next)) ::
            Exec.retainedTargetTurnsFrom ca framePath (nextChild + 1) next committed
termination_by sizeOf run

/-- Select by storage owner. A selected target root emits once and stops the
outer traversal; a failing ancestor settlement discards its entire subtree. -/
def Exec.retainedTargetTurns (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.RetainedTargetTurn :=
  if h : Execution.commits out = true then
    Exec.retainedTargetTurnsFrom ca [] 0 run h
  else []

private theorem Exec.retainedTargetTurnsFrom_target_expand
    (ca : Adr) (framePath : List Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (target : sevm.currentTarget = ca) :
    (Exec.retainedTargetTurnsFrom ca framePath 0 run committed).flatMap
        Exec.RetainedTargetTurn.expand = Exec.stateBoundariesOfCommits framePath 0 run committed := by
  rw [Exec.retainedTargetTurnsFrom, ite_eq_left target]
  simp only [List.flatMap_cons, List.flatMap_nil, Exec.RetainedTargetTurn.expand, List.append_nil]
  rfl

private theorem Exec.retainedTargetTurnsFrom_expand
    (ca : Adr) (framePath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (entryCounter : sevm.currentTarget = ca → nextChild = 0) :
    (Exec.retainedTargetTurnsFrom ca framePath nextChild run committed).flatMap
        Exec.RetainedTargetTurn.expand =
      Exec.stateBoundariesOfCommits framePath nextChild run committed := by
  induction run generalizing framePath nextChild with
  | halt step =>
      by_cases target : (Exec.Frame.ofRun (.halt step) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · obtain rfl := entryCounter target
        exact Exec.retainedTargetTurnsFrom_target_expand ca framePath (.halt step) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, List.flatMap_nil,
          Exec.RetainedTargetTurn.expand, List.append_nil]
  | cont step next ih =>
      by_cases target : (Exec.Frame.ofRun (.cont step next) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · obtain rfl := entryCounter target
        exact Exec.retainedTargetTurnsFrom_target_expand ca framePath (.cont step next) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.RetainedTargetTurn.expand,
          List.singleton_append]
        exact congrArg (List.cons _) (ih framePath nextChild committed
          (fun own => (target own).elim))
  | doneErr step enter resume => simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resume next ih =>
      by_cases target : (Exec.Frame.ofRun (.doneOk step enter resume next) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · obtain rfl := entryCounter target
        exact Exec.retainedTargetTurnsFrom_target_expand ca framePath
          (.doneOk step enter resume next) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.RetainedTargetTurn.expand,
          List.singleton_append]
        exact congrArg (List.cons _) (ih framePath (nextChild + 1) committed
          (fun own => (target own).elim))
  | runErr step enter child resume ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | runOk step enter child resume next childIh nextIh =>
      by_cases target : (Exec.Frame.ofRun (.runOk step enter child resume next) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · obtain rfl := entryCounter target
        exact Exec.retainedTargetTurnsFrom_target_expand ca framePath
          (.runOk step enter child resume next) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [Exec.stateBoundariesOfCommits]
        split
        next settles =>
          simp only [List.flatMap_cons, List.flatMap_append, Exec.RetainedTargetTurn.expand,
            List.singleton_append]
          rw [childIh (framePath ++ [nextChild]) 0 _ (fun _ => rfl),
            nextIh framePath (nextChild + 1) committed (fun own => (target own).elim)]
        next rollsBack =>
          simp only [List.flatMap_cons, Exec.RetainedTargetTurn.expand, List.singleton_append]
          rw [nextIh framePath (nextChild + 1) committed (fun own => (target own).elim)]

/-- Exact ordered expansion preserves every original boundary and occurrence,
including multiplicity, child counters and complete ancestor rollback pruning. -/
theorem Exec.retainedTargetTurns_expand (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (Exec.retainedTargetTurns ca run).flatMap Exec.RetainedTargetTurn.expand =
      Exec.committedStateBoundaries run := by
  unfold Exec.retainedTargetTurns Exec.committedStateBoundaries
  split
  next committed => exact Exec.retainedTargetTurnsFrom_expand ca [] 0 run committed (fun _ => rfl)
  next notCommitted => rfl

private theorem Exec.retainedTargetTurnsFrom_target_spec
    (ca : Adr) (framePath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (target : sevm.currentTarget = ca) :
    let selected := (Exec.retainedTargetTurnsFrom ca framePath nextChild run committed).filterMap
      Sum.getRight?
    (selected <+ ⟨framePath, Exec.Frame.ofRun run committed⟩ ::
      Exec.descendantFramePaths framePath nextChild run) ∧
    (sevm.currentTarget ≠ ca → selected <+ Exec.descendantFramePaths framePath nextChild run) ∧
    (∀ frame ∈ selected, frame.frame.sevm.currentTarget = ca) ∧
    ∀ boundary, Sum.inl boundary ∈ Exec.retainedTargetTurnsFrom ca framePath nextChild run committed →
      boundary.origin.driver.sevm.currentTarget ≠ ca := by
  rw [Exec.retainedTargetTurnsFrom, ite_eq_left target]
  simp only [List.filterMap_cons, List.filterMap_nil, Sum.getRight?_inr]
  refine ⟨(List.nil_sublist _).cons_cons _, fun foreign => (foreign target).elim, ?_, ?_⟩
  · intro frame member
    obtain rfl := List.mem_singleton.mp member
    exact target
  · intro boundary member
    have eq := List.mem_singleton.mp member
    cases eq

private theorem Exec.retainedTargetTurnsFrom_targets_spec
    (ca : Adr) (framePath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    let selected := (Exec.retainedTargetTurnsFrom ca framePath nextChild run committed).filterMap
      Sum.getRight?
    (selected <+ ⟨framePath, Exec.Frame.ofRun run committed⟩ ::
      Exec.descendantFramePaths framePath nextChild run) ∧
    (sevm.currentTarget ≠ ca → selected <+ Exec.descendantFramePaths framePath nextChild run) ∧
    (∀ frame ∈ selected, frame.frame.sevm.currentTarget = ca) ∧
    ∀ boundary, Sum.inl boundary ∈ Exec.retainedTargetTurnsFrom ca framePath nextChild run committed →
      boundary.origin.driver.sevm.currentTarget ≠ ca := by
  induction run generalizing framePath nextChild with
  | halt step =>
      by_cases target : (Exec.Frame.ofRun (.halt step) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · exact Exec.retainedTargetTurnsFrom_target_spec ca framePath nextChild (.halt step) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [List.filterMap_cons, List.filterMap_nil, Sum.getRight?_inl,
          Exec.descendantFramePaths]
        refine ⟨(List.Sublist.refl []).cons _, fun _ => .refl [],
          fun _ member => (List.not_mem_nil member).elim, ?_⟩
        intro boundary member
        obtain rfl := Sum.inl.inj (List.mem_singleton.mp member)
        exact target
  | cont step next ih =>
      by_cases target : (Exec.Frame.ofRun (.cont step next) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · exact Exec.retainedTargetTurnsFrom_target_spec ca framePath nextChild (.cont step next) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [List.filterMap_cons, Sum.getRight?_inl, Exec.descendantFramePaths]
        have tail := ih framePath nextChild committed
        have sub := tail.2.1 target
        refine ⟨sub.cons _, fun _ => sub, tail.2.2.1, ?_⟩
        intro boundary member
        rcases List.mem_cons.mp member with same | member
        · obtain rfl := Sum.inl.inj same
          exact target
        · exact tail.2.2.2 boundary member
  | doneErr step enter resume => simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resume next ih =>
      by_cases target : (Exec.Frame.ofRun (.doneOk step enter resume next) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · exact Exec.retainedTargetTurnsFrom_target_spec ca framePath nextChild
          (.doneOk step enter resume next) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [List.filterMap_cons, Sum.getRight?_inl, Exec.descendantFramePaths]
        have tail := ih framePath (nextChild + 1) committed
        have sub := tail.2.1 target
        refine ⟨sub.cons _, fun _ => sub, tail.2.2.1, ?_⟩
        intro boundary member
        rcases List.mem_cons.mp member with same | member
        · obtain rfl := Sum.inl.inj same
          exact target
        · exact tail.2.2.2 boundary member
  | runErr step enter child resume ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | runOk step enter child resume next childIh nextIh =>
      by_cases target : (Exec.Frame.ofRun (.runOk step enter child resume next) committed).sevm.currentTarget = ca
      all_goals dsimp only [Exec.Frame.ofRun] at target
      · exact Exec.retainedTargetTurnsFrom_target_spec ca framePath nextChild
          (.runOk step enter child resume next) committed target
      · rw [Exec.retainedTargetTurnsFrom, ite_eq_right target]
        simp only [Exec.descendantFramePaths]
        split
        next settles =>
          simp only [List.filterMap_cons, List.filterMap_append, Sum.getRight?_inl]
          have head := childIh (framePath ++ [nextChild]) 0
            (Frame.raw_commits_of_settlementCommits settles)
          have tail := nextIh framePath (nextChild + 1) committed
          have sub := head.1.append (tail.2.1 target)
          refine ⟨sub.cons _, fun _ => sub, ?_, ?_⟩
          · intro frame member
            rcases List.mem_append.mp member with member | member
            · exact head.2.2.1 frame member
            · exact tail.2.2.1 frame member
          · intro boundary member
            rcases List.mem_cons.mp member with same | member
            · obtain rfl := Sum.inl.inj same
              exact target
            · rcases List.mem_append.mp member with childMember | member
              · exact head.2.2.2 boundary childMember
              · rcases List.mem_cons.mp member with same | member
                · obtain rfl := Sum.inl.inj same
                  exact target
                · exact tail.2.2.2 boundary member
        next rollsBack =>
          simp only [List.filterMap_cons, Sum.getRight?_inl, List.nil_append]
          have tail := nextIh framePath (nextChild + 1) committed
          have sub := tail.2.1 target
          refine ⟨sub.cons _, fun _ => sub, tail.2.2.1, ?_⟩
          intro boundary member
          rcases List.mem_cons.mp member with same | member
          · obtain rfl := Sum.inl.inj same
            exact target
          · exact tail.2.2.2 boundary member

/-- Selected targets remain an ordered sublist of the original located-frame
traversal, with identical paths, frame witnesses and multiplicity. -/
theorem Exec.retainedTargetTurns_spec (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    ((Exec.retainedTargetTurns ca run).filterMap Sum.getRight? <+ Exec.committedFramePaths run) ∧
      (∀ frame ∈ (Exec.retainedTargetTurns ca run).filterMap Sum.getRight?,
        frame.frame.sevm.currentTarget = ca) ∧
      ∀ boundary, Sum.inl boundary ∈ Exec.retainedTargetTurns ca run →
        boundary.origin.driver.sevm.currentTarget ≠ ca := by
  unfold Exec.retainedTargetTurns Exec.committedFramePaths
  split
  next committed =>
    have selected := Exec.retainedTargetTurnsFrom_targets_spec ca [] 0 run committed
    exact ⟨selected.1, selected.2.2⟩
  next notCommitted =>
    exact ⟨.refl [], fun _ member => (List.not_mem_nil member).elim,
      fun _ member => (List.not_mem_nil member).elim⟩

/-- A committing target root produces one turn and does not select its nested
frames again in the outer queue. Their actual chronology belongs to its expansion. -/
theorem Exec.retainedTargetTurns_target_stop (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (target : sevm.currentTarget = ca) :
    Exec.retainedTargetTurns ca run = [.inr ⟨[], Exec.Frame.ofRun run committed⟩] := by
  rw [Exec.retainedTargetTurns, dite_eq_left committed,
    Exec.retainedTargetTurnsFrom, ite_eq_left target]

/-- Every selected non-root target carries the actual retained entering
occurrence of its exact original path/frame pair. -/
theorem Exec.retainedTargetTurns_entering (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (frame : Exec.LocatedFrame)
    (selected : frame ∈ (Exec.retainedTargetTurns ca run).filterMap Sum.getRight?)
    (nonroot : frame.path ≠ []) :
    sevm.currentTarget ≠ ca ∧ frame.frame.sevm.currentTarget = ca ∧
      Nonempty (Exec.LocatedFrame.EnteringOccurrence run frame) := by
  have foreignRoot : sevm.currentTarget ≠ ca := by
    intro target
    by_cases committed : Execution.commits out = true
    · rw [Exec.retainedTargetTurns_target_stop ca run committed target] at selected
      simp only [List.filterMap_cons, List.filterMap_nil, Sum.getRight?_inr] at selected
      obtain rfl := List.mem_singleton.mp selected
      exact nonroot rfl
    · simp only [Exec.retainedTargetTurns, dite_eq_right committed, List.filterMap_nil] at selected
      exact (List.not_mem_nil selected).elim
  obtain ⟨ordered, owned, _⟩ := Exec.retainedTargetTurns_spec ca run
  exact ⟨foreignRoot, owned frame selected,
    Exec.LocatedFrame.exists_enteringOccurrence run frame (ordered.subset selected) nonroot⟩

/-- Relevant raw boundaries either belong to the target storage owner or emit
an actual successful LOG. Foreign settlement seams do not copy child LOGs. -/
def Exec.StateBoundary.targetOrLog (ca : Adr) (boundary : Exec.StateBoundary) : Bool :=
  decide (boundary.origin.driver.sevm.currentTarget = ca) ||
    !(Exec.boundaryOwnLogs boundary).isEmpty

/-- Ordered relevant coverage follows from exact expansion. Every uncollapsed
foreign turn passes the relevance filter precisely when it emits an actual LOG. -/
theorem Exec.retainedTargetTurns_cover (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    ((Exec.retainedTargetTurns ca run).flatMap Exec.RetainedTargetTurn.expand).filter
        (Exec.StateBoundary.targetOrLog ca) =
      (Exec.committedStateBoundaries run).filter (Exec.StateBoundary.targetOrLog ca) ∧
    ∀ boundary, Sum.inl boundary ∈ Exec.retainedTargetTurns ca run →
      Exec.StateBoundary.targetOrLog ca boundary = !(Exec.boundaryOwnLogs boundary).isEmpty := by
  refine ⟨congrArg (List.filter (Exec.StateBoundary.targetOrLog ca))
    (Exec.retainedTargetTurns_expand ca run), ?_⟩
  intro boundary member
  have foreign := (Exec.retainedTargetTurns_spec ca run).2.2 boundary member
  rw [Exec.StateBoundary.targetOrLog, decide_eq_false foreign, Bool.false_or]

/-- Canonical semantic cuts of the actual expanded target/foreign queue. -/
noncomputable def Exec.retainedTargetCanonicalChunks (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List (ReplayChunk Exec.StateBoundaryOrigin) :=
  Exec.canonicalChunks ((Exec.retainedTargetTurns ca run).flatMap Exec.RetainedTargetTurn.expand)

/-- Consume the actual expanded queue using one local canonical chunk at a time.
Original ordered target/foreign provenance is supplied to local producers; no
selected frame's desired model endpoint or independently supplied trace is assumed. -/
theorem Exec.simulateRetainedTargetLogChunks
    {Q Step : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List Log) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork)
    (Link : List (ReplayChunk Exec.StateBoundaryOrigin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] pre.state q₀)
    (localStep :
      ((Exec.retainedTargetTurns ca run).filterMap Sum.getRight? <+ Exec.committedFramePaths run) →
      (∀ frame ∈ (Exec.retainedTargetTurns ca run).filterMap Sum.getRight?,
        frame.frame.sevm.currentTarget = ca ∧
          (frame.path ≠ [] → sevm.currentTarget ≠ ca ∧
            Nonempty (Exec.LocatedFrame.EnteringOccurrence run frame))) →
      (∀ boundary, Sum.inl boundary ∈ Exec.retainedTargetTurns ca run →
        boundary.origin.driver.sevm.currentTarget ≠ ca) →
      (∀ boundary, Sum.inl boundary ∈ Exec.retainedTargetTurns ca run →
        Exec.StateBoundary.targetOrLog ca boundary = !(Exec.boundaryOwnLogs boundary).isEmpty) →
      ∀ prior chunk suffix,
        Exec.retainedTargetCanonicalChunks ca run = prior ++ chunk :: suffix →
        Exec.AdmissibleChunk chunk → ∀ q, Link prior chunk.before q →
        ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
          obs steps = chunk.origin.flatMap Exec.boundaryOwnLogs) :
    ∃ q' steps, R q₀ steps q' ∧
      Link (Exec.retainedTargetCanonicalChunks ca run)
        (Execution.committedPost out committed).state q' ∧
      obs steps = (Exec.retainedTargetTurns ca run).flatMap
        (fun turn => turn.expand.flatMap Exec.boundaryOwnLogs) ∧
      (Execution.committedPost out committed).logs = pre.logs ++ obs steps := by
  have cuts : Exec.retainedTargetCanonicalChunks ca run = Exec.committedCanonicalChunks run := by
    unfold Exec.retainedTargetCanonicalChunks Exec.committedCanonicalChunks
    rw [Exec.retainedTargetTurns_expand]
  obtain ⟨ordered, owned, foreign⟩ := Exec.retainedTargetTurns_spec ca run
  have provenance : ∀ frame ∈ (Exec.retainedTargetTurns ca run).filterMap Sum.getRight?,
      frame.frame.sevm.currentTarget = ca ∧
        (frame.path ≠ [] → sevm.currentTarget ≠ ca ∧
          Nonempty (Exec.LocatedFrame.EnteringOccurrence run frame)) := by
    intro frame member
    refine ⟨owned frame member, ?_⟩
    intro nonroot
    have entered := Exec.retainedTargetTurns_entering ca run frame member nonroot
    exact ⟨entered.1, entered.2.2⟩
  obtain ⟨q', steps, model, ending, observations, logs⟩ :=
    Exec.simulateCanonicalLogChunks R nil append obs obs_nil obs_append run committed fork Link opening
      (fun prior chunk suffix aligned admissible q cut =>
        localStep ordered provenance foreign (Exec.retainedTargetTurns_cover ca run).2
          prior chunk suffix (cuts.trans aligned) admissible q cut)
  refine ⟨q', steps, model, ?_, ?_, logs⟩
  · rw [cuts]
    exact ending
  · rw [← Exec.retainedTargetTurns_expand ca run] at observations
    simpa only [List.flatMap_assoc] using observations

namespace ExecutionTrace

private def MessageStateBoundaryOrigin.execution? :
    MessageStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .wrapper .. => none
  | .execution _ origin => some origin

private def SystemMessageStateBoundaryOrigin.execution? :
    SystemMessageStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .preparation .. => none
  | .message _ origin => MessageStateBoundaryOrigin.execution? origin

private def TransactionStateBoundaryOrigin.execution? :
    TransactionStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .message _ origin => MessageStateBoundaryOrigin.execution? origin
  | _ => none

private def RequestsStateBoundaryOrigin.execution? :
    RequestsStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .withdrawal _ origin => SystemMessageStateBoundaryOrigin.execution? origin
  | .consolidation _ origin => SystemMessageStateBoundaryOrigin.execution? origin

private def AppliedBodyStateBoundaryOrigin.execution? :
    AppliedBodyStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .beacon _ origin => SystemMessageStateBoundaryOrigin.execution? origin
  | .history _ origin => SystemMessageStateBoundaryOrigin.execution? origin
  | .transaction _ origin => TransactionStateBoundaryOrigin.execution? origin
  | .withdrawal .. => none
  | .request _ origin => RequestsStateBoundaryOrigin.execution? origin

private def ConfiguredBlockStateBoundary.execution?
    (boundary : ConfiguredBlockStateBoundary) : Option Exec.StateBoundary :=
  let origin := match boundary.origin with
    | .preparation .. => none
    | .body _ origin => AppliedBodyStateBoundaryOrigin.execution? origin
  origin.map (fun raw =>
    { origin := raw, before := boundary.before, after := boundary.after })

/-- Every raw member retains the exact corresponding wrapper boundary.  A raw
chunk may contain no wrapper seam; nonexecution wrappers are singleton cuts. -/
def ConfiguredAdmissibleChunk
    (chunk : ReplayChunk ConfiguredBlockStateBoundaryOrigin) : Prop :=
  (∃ raw, List.Forall₂
      (fun boundary event => ConfiguredBlockStateBoundary.execution? boundary = some event)
      chunk.origin raw ∧
      Exec.AdmissibleChunk { origin := raw, before := chunk.before, after := chunk.after }) ∨
  (∃ boundary, chunk.origin = [boundary] ∧
    ConfiguredBlockStateBoundary.execution? boundary = none)

private def ConfiguredBlockStateBoundary.canPrepend
    (boundary : ConfiguredBlockStateBoundary)
    (chunk : ReplayChunk ConfiguredBlockStateBoundaryOrigin) : Prop :=
  ∃ event raw,
    ConfiguredBlockStateBoundary.execution? boundary = some event ∧
    List.Forall₂
      (fun boundary event => ConfiguredBlockStateBoundary.execution? boundary = some event)
      chunk.origin raw ∧ Exec.canPrepend event
        {origin := raw, before := chunk.before, after := chunk.after}

private theorem configured_singleton_admissible (boundary : ConfiguredBlockStateBoundary) :
    ConfiguredAdmissibleChunk
      {origin := [boundary], before := boundary.before, after := boundary.after} := by
  cases decoded : ConfiguredBlockStateBoundary.execution? boundary with
  | none => exact Or.inr ⟨boundary, rfl, decoded⟩
  | some event =>
      exact Or.inl ⟨[event], .cons decoded .nil, Exec.singleton_admissible event⟩

private theorem configured_prepend_admissible
    (boundary : ConfiguredBlockStateBoundary)
    (chunk : ReplayChunk ConfiguredBlockStateBoundaryOrigin)
    (can : ConfiguredBlockStateBoundary.canPrepend boundary chunk)
    (admissible : ConfiguredAdmissibleChunk chunk) :
    ConfiguredAdmissibleChunk
      {origin := boundary :: chunk.origin, before := boundary.before, after := chunk.after} := by
  obtain ⟨event, raw, decoded, mapped, own⟩ := can
  rcases admissible with ⟨raw', mapped', rawAdmissible⟩ | ⟨seam, eq, noExecution⟩
  · have same : raw = raw' := List.right_unique_forall₂'
      (fun _ _ _ first second => Option.some.inj (first.symm.trans second)) mapped mapped'
    subst raw'
    exact Or.inl ⟨event :: raw, .cons decoded mapped,
      Exec.prepend_admissible own rawAdmissible⟩
  · rw [eq] at mapped
    cases mapped with
    | cons head tail => rw [noExecution] at head; contradiction

/-- Canonical cuts retain the original configured wrappers; each raw execution
segment obeys the same semantic policy, and every wrapper seam is a singleton. -/
noncomputable def ConfiguredHistoryStateChronology.canonicalChunks
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history) :
    List (ReplayChunk ConfiguredBlockStateBoundaryOrigin) :=
  StateTransition.canonicalChunks ConfiguredBlockStateBoundary.canPrepend chronology.stateBoundaries

/-- Both flattening/endpoints and semantic cuts follow from the actual configured
chronology, without a supplied partition or a second history state chain. -/
theorem ConfiguredHistoryStateChronology.canonicalChunks_spec
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history) :
    ExactChunks chronology.stateBoundaries chronology.canonicalChunks ∧
      ∀ chunk ∈ chronology.canonicalChunks, ConfiguredAdmissibleChunk chunk :=
  ⟨StateReplay.canonicalChunks_exact ConfiguredBlockStateBoundary.canPrepend chronology.stateReplay,
    StateTransition.canonicalChunks_satisfies ConfiguredBlockStateBoundary.canPrepend
      ConfiguredAdmissibleChunk configured_singleton_admissible configured_prepend_admissible _⟩

/-- Specialize the exact local fold to the actual configured history, with
coverage at each retained block supplied by its existing chronology witness.
No independently supplied state chain or whole-run model endpoint is used. -/
theorem ConfiguredHistoryStateChronology.simulateChunks
    {Q Step O : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List O) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (actual : ConfiguredBlockStateBoundary → List O)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history)
    {chunks : List (ReplayChunk ConfiguredBlockStateBoundaryOrigin)}
    (exactChunks : ExactChunks chronology.stateBoundaries chunks)
    (admissible : ∀ chunk ∈ chunks, ConfiguredAdmissibleChunk chunk)
    (Link : List (ReplayChunk ConfiguredBlockStateBoundaryOrigin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] checkpoint.state q₀)
    (localStep : ∀ prior chunk suffix,
      chunks = prior ++ chunk :: suffix → ConfiguredAdmissibleChunk chunk →
      ∀ q, Link prior chunk.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
        obs steps = chunk.origin.flatMap actual) :
    ∃ q' steps, R q₀ steps q' ∧ Link chunks future.state q' ∧
      obs steps = chronology.stateBoundaries.flatMap actual := by
  apply chronology.stateReplay.simulateChunks
    R nil append obs obs_nil obs_append actual exactChunks Link opening
  intro prior chunk suffix aligned q cut
  have member : chunk ∈ chunks := by
    rw [aligned]
    exact List.mem_append_right prior List.mem_cons_self
  exact localStep prior chunk suffix aligned (admissible chunk member) q cut

/-- The configured local fold consumes its actual canonical admissible cuts,
including original block/message wrappers and each retained fork witness. -/
theorem ConfiguredHistoryStateChronology.simulateCanonicalChunks
    {Q Step O : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List O) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (actual : ConfiguredBlockStateBoundary → List O)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history)
    (Link : List (ReplayChunk ConfiguredBlockStateBoundaryOrigin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] checkpoint.state q₀)
    (localStep : ∀ prior chunk suffix,
      chronology.canonicalChunks = prior ++ chunk :: suffix → ConfiguredAdmissibleChunk chunk →
      ∀ q, Link prior chunk.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
        obs steps = chunk.origin.flatMap actual) :
    ∃ q' steps, R q₀ steps q' ∧ Link chronology.canonicalChunks future.state q' ∧
      obs steps = chronology.stateBoundaries.flatMap actual := by
  obtain ⟨exactCuts, admissible⟩ := chronology.canonicalChunks_spec
  exact chronology.simulateChunks R nil append obs obs_nil obs_append actual
    exactCuts admissible Link opening localStep

end ExecutionTrace

end Blanc
