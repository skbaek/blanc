import Blanc.ExecutionOccurrence

/-!
Contract-neutral call-tree paths for settlement-retained execution frames.
The path index counts every entered or immediately completed child message at
its parent, including children later pruned by settlement, so deleting a
failed sibling cannot silently renumber the surviving execution provenance.
-/

namespace Blanc

open Jaune

/-- A settlement-retained execution frame paired with its call-tree path.  The
selected root has path `[]`; a recursively executed child appends its
zero-based sibling index. -/
structure Exec.LocatedFrame where
  path : List Nat
  frame : Exec.Frame

/-- Settlement-retained descendant frames with call-tree paths.  `nextChild`
counts all child messages already encountered in the current parent. -/
def Exec.descendantFramePaths (parentPath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.LocatedFrame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.descendantFramePaths parentPath nextChild next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next =>
      Exec.descendantFramePaths parentPath (nextChild + 1) next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childPath := parentPath ++ [nextChild]
      let childFrames :=
        if h : Blanc.Frame.settlementCommits frame raw = true then
          ⟨childPath, Exec.Frame.ofRun child
            (Blanc.Frame.raw_commits_of_settlementCommits h)⟩ ::
              Exec.descendantFramePaths childPath 0 child
        else []
      childFrames ++
        Exec.descendantFramePaths parentPath (nextChild + 1) next
termination_by sizeOf run

/-- All and only settlement-retained frames, annotated by their stable
call-tree paths. -/
def Exec.committedFramePaths
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.LocatedFrame :=
  if h : Execution.commits out = true then
    ⟨[], Exec.Frame.ofRun run h⟩ :: Exec.descendantFramePaths [] 0 run
  else []

/-- The exact same-frame instruction occurrence which entered one retained
child frame.  `childIndex` is the parent traversal's actual child counter:
it counts every entered or immediately completed child before this spawn.
The witness deliberately leaves the instruction family unconstrained; a
consumer may refine `occurrence.decoded` and `occurrence.stepRun` to CALL,
STATICCALL, CREATE, or another spawning instruction. -/
structure Exec.LocatedFrame.EnteringOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (root : Exec pc sevm pre out) (child : Exec.LocatedFrame) : Type where
  /-- The retained frame whose same-frame execution entered `child`. -/
  parent : Exec.LocatedFrame
  /-- This exact path/frame pair occurs in the original root traversal.  This
  preserves provenance when structurally equal frames occur more than once. -/
  parentMember : parent ∈ Exec.committedFramePaths root
  /-- The actual zero-based position at which the parent entered `child`. -/
  childIndex : Nat
  /-- The committed-path constructor records that exact spawn position. -/
  path_eq : child.path = parent.path ++ [childIndex]
  /-- The parent instruction which entered the child. -/
  occurrence : Exec.NinstOccurrence parent.frame.rootDeriv
  /-- The entering node lies in the parent's own continuation, not a nested
  child frame. -/
  sameFrame : Exec.Deriv.ParentPrefix parent.frame.rootDeriv occurrence.node
  /-- The entering instruction itself survived complete settlement. -/
  retained : occurrence.Retained
  /-- Its recursive slot is the selected child's exact EVM and raw outcome. -/
  slot_eq : occurrence.slot = .some
    ⟨⟨child.frame.pc, child.frame.sevm, child.frame.pre⟩, child.frame.out⟩
  /-- The selected frame's actual derivation is the child premise of the
  entering `runOk`, including the exact frame entry and resume equations. -/
  spawns : ∃ (frame : Jaune.Frame) (resume : Resume) (nextPc : Nat)
      (post : Devm)
      (step : Evm.step
        ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
          .spawn frame resume nextPc)
      (entered : frame.enter = .run
        ⟨child.frame.pc, child.frame.sevm, child.frame.pre⟩)
      (resumed : resume.run (frame.settle child.frame.out) = .ok post)
      (next : Exec nextPc occurrence.node.sevm post occurrence.node.exn),
      occurrence.node.exc =
        .runOk step entered child.frame.run resumed next

/-- Path annotation is conservative: erasing paths yields the established
settlement-retained frame traversal exactly, with identical order and pruning. -/
private theorem Exec.descendantFramePaths_map_frame
    (parentPath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (Exec.descendantFramePaths parentPath nextChild run).map
        Exec.LocatedFrame.frame =
      Exec.descendantFrames run := by
  induction run generalizing parentPath nextChild with
  | halt =>
      simp [Exec.descendantFramePaths, Exec.descendantFrames]
  | cont hstep next ih =>
      simpa [Exec.descendantFramePaths, Exec.descendantFrames] using
        ih (parentPath := parentPath) (nextChild := nextChild)
  | doneErr =>
      simp [Exec.descendantFramePaths, Exec.descendantFrames]
  | doneOk hstep henter hresume next ih =>
      simpa [Exec.descendantFramePaths, Exec.descendantFrames] using
        ih (parentPath := parentPath) (nextChild := nextChild + 1)
  | runErr =>
      simp [Exec.descendantFramePaths, Exec.descendantFrames]
  | runOk hstep henter child hresume next childIh nextIh =>
      simp only [Exec.descendantFramePaths, Exec.descendantFrames,
        List.map_append]
      split
      next childSettles =>
        simp only [List.map_cons]
        rw [childIh, nextIh]
      next childDoesNotSettle =>
        simp only [List.map_nil, List.nil_append]
        exact nextIh parentPath (nextChild + 1)

/-- Forgetting every path recovers `Exec.committedFrames` definitionally up to
the recursive annotation erasure. -/
theorem Exec.committedFramePaths_map_frame
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (Exec.committedFramePaths run).map Exec.LocatedFrame.frame =
      Exec.committedFrames run := by
  unfold Exec.committedFramePaths Exec.committedFrames
  split
  next committed =>
    simp only [List.map_cons]
    rw [Exec.descendantFramePaths_map_frame]
  next notCommitted =>
    rfl

/-- A retained descendant path remembers the exact same-frame spawn that
entered it.  The private traversal keeps the parent frame and its continuation
prefix explicit while it follows child-before-parent-resumption order.  Its
membership transport always targets the original root traversal. -/
private theorem Exec.descendantFramePaths_entering
    {rootPc : Nat} {rootSevm : Sevm} {rootPre : Devm} {rootOut : Execution}
    (root : Exec rootPc rootSevm rootPre rootOut)
    (rootCommitted : Execution.commits rootOut = true)
    (parentPath : List Nat)
    {parentPc : Nat} {parentSevm : Sevm} {parentPre : Devm}
    {parentOut : Execution}
    (parentRun : Exec parentPc parentSevm parentPre parentOut)
    (parentCommitted : Execution.commits parentOut = true)
    (parentMember : ⟨parentPath, Exec.Frame.ofRun parentRun parentCommitted⟩ ∈
      Exec.committedFramePaths root)
    {pc : Nat} {pre : Devm}
    (current : Exec pc parentSevm pre parentOut)
    (sameFramePrefix : Exec.Deriv.ParentPrefix
      (Exec.Frame.ofRun parentRun parentCommitted).rootDeriv
      ⟨pc, parentSevm, pre, parentOut, current⟩)
    (nextChild : Nat) (child : Exec.LocatedFrame)
    (descendantsMember : ∀ descendant,
      descendant ∈ Exec.descendantFramePaths parentPath nextChild current →
      descendant ∈ Exec.committedFramePaths root)
    (member : child ∈ Exec.descendantFramePaths parentPath nextChild current) :
    Nonempty (Exec.LocatedFrame.EnteringOccurrence root child) := by
  cases current with
  | halt hstep =>
      simp [Exec.descendantFramePaths] at member
  | cont hstep next =>
      let edge : Exec.Deriv.ParentStep
          (⟨_, parentSevm, _, parentOut, next⟩ : Exec.Deriv)
          (⟨_, parentSevm, _, parentOut,
            Exec.cont hstep next⟩ : Exec.Deriv) := .cont hstep next
      apply Exec.descendantFramePaths_entering root rootCommitted parentPath
        parentRun parentCommitted parentMember next
        (sameFramePrefix.snoc edge) nextChild child
      · intro descendant descendantMember
        apply descendantsMember descendant
        simpa [Exec.descendantFramePaths] using descendantMember
      · simpa [Exec.descendantFramePaths] using member
  | doneErr hstep henter hresume =>
      simp [Exec.descendantFramePaths] at member
  | doneOk hstep henter hresume next =>
      let edge : Exec.Deriv.ParentStep
          (⟨_, parentSevm, _, parentOut, next⟩ : Exec.Deriv)
          (⟨_, parentSevm, _, parentOut,
            Exec.doneOk hstep henter hresume next⟩ : Exec.Deriv) :=
        .doneOk hstep henter hresume next
      apply Exec.descendantFramePaths_entering root rootCommitted parentPath
        parentRun parentCommitted parentMember next
        (sameFramePrefix.snoc edge) (nextChild + 1) child
      · intro descendant descendantMember
        apply descendantsMember descendant
        simpa [Exec.descendantFramePaths] using descendantMember
      · simpa [Exec.descendantFramePaths] using member
  | runErr hstep henter exec hresume =>
      simp [Exec.descendantFramePaths] at member
  | runOk hstep henter exec hresume next =>
      rename_i frame resume nextPc childEvm raw post
      simp only [Exec.descendantFramePaths] at member
      split at member
      next childSettles =>
        have childCommitted : Execution.commits raw = true :=
          Frame.raw_commits_of_settlementCommits childSettles
        have childMember :
            ⟨parentPath ++ [nextChild],
              Exec.Frame.ofRun exec childCommitted⟩ ∈
              Exec.committedFramePaths root := by
          apply descendantsMember
          simp [Exec.descendantFramePaths, childSettles]
        have splitMember :
            child = ⟨parentPath ++ [nextChild],
              Exec.Frame.ofRun exec childCommitted⟩ ∨
              child ∈ Exec.descendantFramePaths
                (parentPath ++ [nextChild]) 0 exec ∨
              child ∈ Exec.descendantFramePaths parentPath (nextChild + 1) next := by
          simpa [Exec.descendantFramePaths, childSettles, List.mem_append]
            using member
        clear member
        rcases splitMember with direct | nested | resumed
        · subst child
          rcases Evm.step_spawn_inv hstep with ⟨instruction, decoded, -, -⟩
          let node : Exec.Deriv :=
            ⟨_, parentSevm, _, parentOut,
              Exec.runOk hstep henter exec hresume next⟩
          have reached : node ∈ Exec.rawNodes
              (Exec.Frame.ofRun parentRun parentCommitted).rootDeriv.exc := by
            obtain ⟨before, chronology⟩ := sameFramePrefix.rawNodes_decomposition
            rw [chronology]
            simp [node, Exec.rawNodes]
          let occurrence : Exec.NinstOccurrence
              (Exec.Frame.ofRun parentRun parentCommitted).rootDeriv :=
            { node := node
              instruction := .exec instruction
              slot := .some ⟨_, raw⟩
              stepResult := .ok _
              reached := reached
              decoded := decoded
              filled := ⟨exec⟩
              stepRun := by
                unfold Ninst.StepRun
                rw [← Evm.step_next decoded, hstep]
                exact ⟨frame.settle raw, RunFrame.of_run henter, hresume.symm⟩ }
          have sameFrame : Exec.Deriv.ParentPrefix
              (Exec.Frame.ofRun parentRun parentCommitted).rootDeriv
              occurrence.node := by
            simpa only [occurrence, node] using sameFramePrefix
          have parentFrameRetained : Exec.Frame.ofRun parentRun parentCommitted ∈
              Exec.committedFrames parentRun := by
            simp [Exec.committedFrames, parentCommitted]
          have retained : occurrence.Retained := by
            unfold Exec.NinstOccurrence.Retained
            apply (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix
              parentRun occurrence.node).mpr
            exact ⟨Exec.Frame.ofRun parentRun parentCommitted,
              parentFrameRetained, sameFrame⟩
          let parent : Exec.LocatedFrame :=
            ⟨parentPath, Exec.Frame.ofRun parentRun parentCommitted⟩
          refine ⟨⟨parent, parentMember, nextChild, rfl, occurrence, sameFrame,
            retained, rfl, ?_⟩⟩
          refine ⟨frame, _, _, _, hstep, henter, hresume, next, ?_⟩
          rfl
        · apply Exec.descendantFramePaths_entering root rootCommitted
            (parentPath ++ [nextChild]) exec childCommitted childMember exec
            (Exec.Deriv.ParentPrefix.refl _) 0 child
          · intro descendant descendantMember
            apply descendantsMember descendant
            simp [Exec.descendantFramePaths, childSettles, List.mem_append,
              descendantMember]
          · exact nested
        · let edge : Exec.Deriv.ParentStep
              (⟨_, parentSevm, _, parentOut, next⟩ : Exec.Deriv)
              (⟨_, parentSevm, _, parentOut,
                Exec.runOk hstep henter exec hresume next⟩ : Exec.Deriv) :=
            .runOk hstep henter exec hresume next
          apply Exec.descendantFramePaths_entering root rootCommitted parentPath
            parentRun parentCommitted parentMember next
            (sameFramePrefix.snoc edge) (nextChild + 1) child
          · intro descendant descendantMember
            apply descendantsMember descendant
            simp [Exec.descendantFramePaths, childSettles, List.mem_append,
              descendantMember]
          · exact resumed
      next childDoesNotSettle =>
        let edge : Exec.Deriv.ParentStep
            (⟨_, parentSevm, _, parentOut, next⟩ : Exec.Deriv)
            (⟨_, parentSevm, _, parentOut,
              Exec.runOk hstep henter exec hresume next⟩ : Exec.Deriv) :=
          .runOk hstep henter exec hresume next
        have resumed : child ∈ Exec.descendantFramePaths
            parentPath (nextChild + 1) next := by
          simpa [Exec.descendantFramePaths, childDoesNotSettle] using member
        apply Exec.descendantFramePaths_entering root rootCommitted parentPath
          parentRun parentCommitted parentMember next
          (sameFramePrefix.snoc edge) (nextChild + 1) child
        · intro descendant descendantMember
          apply descendantsMember descendant
          simp [Exec.descendantFramePaths, childDoesNotSettle, descendantMember]
        · exact resumed
termination_by sizeOf current

/-- Every non-root member of a committed frame-path traversal has the exact
same-frame instruction occurrence that entered it.  The root path `[]` is
intentionally excluded: an arbitrary raw message may itself target the child
account, so an external transaction or system-message envelope must handle
that case separately. -/
theorem Exec.LocatedFrame.exists_enteringOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (child : Exec.LocatedFrame)
    (member : child ∈ Exec.committedFramePaths run)
    (nonroot : child.path ≠ []) :
    Nonempty (Exec.LocatedFrame.EnteringOccurrence run child) := by
  unfold Exec.committedFramePaths at member
  split at member
  next committed =>
    simp only [List.mem_cons] at member
    rcases member with root | descendant
    · apply False.elim
      apply nonroot
      simp only [root]
    · have rootMember :
          ⟨[], Exec.Frame.ofRun run committed⟩ ∈ Exec.committedFramePaths run := by
        simp [Exec.committedFramePaths, committed]
      apply Exec.descendantFramePaths_entering run committed [] run committed
        rootMember run (Exec.Deriv.ParentPrefix.refl _) 0 child
      · intro candidate candidateMember
        simp [Exec.committedFramePaths, committed, candidateMember]
      · exact descendant
  next notCommitted => simp at member

end Blanc
