import Blanc.ExecutionSettlement
import Blanc.Compiled
import Blanc.CommonProofs
import Blanc.ExecDeterminism
import Blanc.Ladder

/-!
Contract-neutral instruction occurrences over finite execution derivations.

The raw chronology records every reached driver node, independently of the
root outcome.  At a spawning node it places the spawning instruction before
the complete child execution and the resumed parent continuation after the
child.  Settlement-aware filtering and compiler/source attribution are built
on this order below.
-/

namespace Blanc

open Jaune

/-- The root derivation bundled by a retained frame. -/
def Exec.Frame.rootDeriv (frame : Exec.Frame) : Exec.Deriv :=
  ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩

/-- Every reached driver node, in execution order.  This is deliberately not
`Exec.Deriv.le`: the child and resumed continuation of `runOk` are sibling
recursive premises, while the chronology orders the child first. -/
def Exec.rawNodes {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Deriv :=
  let root : Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Exec.rawNodes next
  | .doneErr _ _ _ => [root]
  | .doneOk _ _ _ next => root :: Exec.rawNodes next
  | .runErr _ _ child _ => root :: Exec.rawNodes child
  | .runOk _ _ child _ next =>
      root :: (Exec.rawNodes child ++ Exec.rawNodes next)
termination_by sizeOf run

/-- Roots of actually entered child code frames, in execution order.  Same-frame
continuations contribute only the child frames that they later enter. -/
def Exec.rawFrameDescendants {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Deriv :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.rawFrameDescendants next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.rawFrameDescendants next
  | .runErr _ _ child _ =>
      ⟨_, _, _, _, child⟩ :: Exec.rawFrameDescendants child
  | .runOk _ _ child _ next =>
      ⟨_, _, _, _, child⟩ ::
        (Exec.rawFrameDescendants child ++ Exec.rawFrameDescendants next)
termination_by sizeOf run

/-- The all-outcome code-frame traversal: the selected outer root followed by
every actually entered child root, with child descendants before roots reached
after the parent resumes.  No commitment or settlement filter is applied. -/
def Exec.rawFrameRoots {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Deriv :=
  ⟨pc, sevm, pre, out, run⟩ :: Exec.rawFrameDescendants run

/-- The selected outer execution always heads its raw-frame traversal. -/
theorem Exec.mem_rawFrameRoots_self
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) ∈
      Exec.rawFrameRoots run := by
  simp [Exec.rawFrameRoots]

/-- A failed parent resume still retains the entered child and all of its raw
descendant frame roots. -/
@[simp] theorem Exec.rawFrameRoots_runErr
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw : Execution} {error : EvmError × Devm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .error error) :
    Exec.rawFrameRoots (.runErr hstep henter child hresume) =
      ⟨pc, sevm, pre, .error error,
        Exec.runErr hstep henter child hresume⟩ ::
        Exec.rawFrameRoots child := by
  simp [Exec.rawFrameRoots, Exec.rawFrameDescendants]

/-- On a successful parent resume, the child's complete raw-frame segment
precedes every child frame entered later by the resumed parent. -/
@[simp] theorem Exec.rawFrameRoots_runOk
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok post)
    (next : Exec pc' sevm post out) :
    Exec.rawFrameRoots (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Exec.runOk hstep henter child hresume next⟩ ::
        (Exec.rawFrameRoots child ++ Exec.rawFrameDescendants next) := by
  simp [Exec.rawFrameRoots, Exec.rawFrameDescendants]

/-- The execution proof itself heads its raw chronology. -/
theorem Exec.mem_rawNodes_self
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) ∈ Exec.rawNodes run := by
  cases run <;> simp [Exec.rawNodes]

/-! ## Settlement-retained chronology -/

/-- The retained node stream of a known-committing execution.  A spawned
child is included only when complete frame settlement commits; in particular,
raw CREATE success is insufficient when code deposit rolls back. -/
def Exec.retainedNodesOfCommits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List Exec.Deriv :=
  let root : Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Exec.retainedNodesOfCommits next committed
  | .doneErr _ _ _ => by simp [Execution.commits] at committed
  | .doneOk _ _ _ next => root :: Exec.retainedNodesOfCommits next committed
  | .runErr _ _ _ _ => by simp [Execution.commits] at committed
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      root ::
        ((if h : Frame.settlementCommits frame raw = true then
            Exec.retainedNodesOfCommits child
              (Frame.raw_commits_of_settlementCommits h)
          else []) ++
          Exec.retainedNodesOfCommits next committed)
termination_by sizeOf run

/-- Public retained chronology.  The whole stream is erased when the root
does not commit, so locally successful work cannot leak through rollback. -/
def Exec.retainedNodes
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.Deriv :=
  if h : Execution.commits out = true then
    Exec.retainedNodesOfCommits run h
  else []

@[simp] theorem Exec.retainedNodes_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : Execution.commits out ≠ true) :
    Exec.retainedNodes run = [] := by
  simp [Exec.retainedNodes, h]

@[simp] theorem Exec.retainedNodes_eq_of_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : Execution.commits out = true) :
    Exec.retainedNodes run = Exec.retainedNodesOfCommits run h := by
  simp [Exec.retainedNodes, h]

@[simp] theorem Exec.retainedNodes_runOk_of_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (rootCommits : Execution.commits out = true)
    (childSettles : Frame.settlementCommits frame raw = true) :
    Exec.retainedNodes (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Exec.runOk hstep henter child hresume next⟩ ::
        (Exec.retainedNodes child ++ Exec.retainedNodes next) := by
  have childCommits := Frame.raw_commits_of_settlementCommits childSettles
  simp [Exec.retainedNodes, Exec.retainedNodesOfCommits, rootCommits,
    childSettles, childCommits]

@[simp] theorem Exec.retainedNodes_runOk_of_not_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (rootCommits : Execution.commits out = true)
    (childDoesNotSettle : Frame.settlementCommits frame raw ≠ true) :
    Exec.retainedNodes (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Exec.runOk hstep henter child hresume next⟩ ::
        Exec.retainedNodes next := by
  simp [Exec.retainedNodes, Exec.retainedNodesOfCommits, rootCommits,
    childDoesNotSettle]

private theorem List.nilSublist {α : Type} (xs : List α) :
    List.Sublist [] xs := by
  induction xs with
  | nil => exact .slnil
  | cons head tail ih => exact ih.cons _

private theorem List.Sublist.appendRight
    {α : Type} {xs ys : List α} (front : List α)
    (h : List.Sublist xs ys) : List.Sublist xs (front ++ ys) := by
  induction front with
  | nil => exact h
  | cons head tail ih => exact ih.cons _

/-- Settlement retention only removes nodes from the raw chronology. -/
theorem Exec.retainedNodesOfCommits_sublist_rawNodes
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List.Sublist (Exec.retainedNodesOfCommits run committed)
      (Exec.rawNodes run) := by
  induction run with
  | halt => simp [Exec.retainedNodesOfCommits, Exec.rawNodes]
  | cont hstep next ih =>
      simp only [Exec.retainedNodesOfCommits, Exec.rawNodes]
      exact (ih committed).cons_cons _
  | doneErr => simp [Execution.commits] at committed
  | doneOk hstep henter hresume next ih =>
      simp only [Exec.retainedNodesOfCommits, Exec.rawNodes]
      exact (ih committed).cons_cons _
  | runErr => simp [Execution.commits] at committed
  | runOk hstep henter child hresume next childIh nextIh =>
      simp only [Exec.retainedNodesOfCommits, Exec.rawNodes]
      split
      next childSettles =>
        exact ((childIh (Frame.raw_commits_of_settlementCommits childSettles)).append
          (nextIh committed)).cons_cons _
      next childDoesNotSettle =>
        exact (List.Sublist.appendRight (Exec.rawNodes child)
          (nextIh committed)).cons_cons _

theorem Exec.retainedNodes_sublist_rawNodes
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    List.Sublist (Exec.retainedNodes run) (Exec.rawNodes run) := by
  unfold Exec.retainedNodes
  split
  next committed => exact run.retainedNodesOfCommits_sublist_rawNodes committed
  next notCommitted => exact List.nilSublist _

private def Exec.retainedTailOfCommits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List Exec.Deriv :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.retainedNodesOfCommits next committed
  | .doneErr _ _ _ => by simp [Execution.commits] at committed
  | .doneOk _ _ _ next => Exec.retainedNodesOfCommits next committed
  | .runErr _ _ _ _ => by simp [Execution.commits] at committed
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      (if h : Frame.settlementCommits frame raw = true then
          Exec.retainedNodesOfCommits child
            (Frame.raw_commits_of_settlementCommits h)
        else []) ++ Exec.retainedNodesOfCommits next committed

private theorem Exec.retainedNodesOfCommits_eq_root_cons
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    Exec.retainedNodesOfCommits run committed =
      ⟨pc, sevm, pre, out, run⟩ ::
        Exec.retainedTailOfCommits run committed := by
  cases run with
  | halt => simp [Exec.retainedNodesOfCommits, Exec.retainedTailOfCommits]
  | cont => simp [Exec.retainedNodesOfCommits, Exec.retainedTailOfCommits]
  | doneErr => simp [Execution.commits] at committed
  | doneOk => simp [Exec.retainedNodesOfCommits, Exec.retainedTailOfCommits]
  | runErr => simp [Execution.commits] at committed
  | runOk => simp [Exec.retainedNodesOfCommits, Exec.retainedTailOfCommits]

private theorem Exec.descendantFrameRoots_sublist_retainedNodesOfCommits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List.Sublist ((Exec.descendantFrames run).map Exec.Frame.rootDeriv)
      (Exec.retainedTailOfCommits run committed) := by
  induction run with
  | halt => simp [Exec.descendantFrames, Exec.retainedTailOfCommits]
  | cont hstep next ih =>
      simp only [Exec.descendantFrames, Exec.retainedTailOfCommits]
      rw [next.retainedNodesOfCommits_eq_root_cons committed]
      exact (ih committed).cons _
  | doneErr => simp [Execution.commits] at committed
  | doneOk hstep henter hresume next ih =>
      simp only [Exec.descendantFrames, Exec.retainedTailOfCommits]
      rw [next.retainedNodesOfCommits_eq_root_cons committed]
      exact (ih committed).cons _
  | runErr => simp [Execution.commits] at committed
  | runOk hstep henter child hresume next childIh nextIh =>
      simp only [Exec.descendantFrames, Exec.retainedTailOfCommits]
      split
      next childSettles =>
        have childCommits :=
          Frame.raw_commits_of_settlementCommits childSettles
        have childFrames : List.Sublist
            ((Exec.Frame.ofRun child childCommits ::
                Exec.descendantFrames child).map Exec.Frame.rootDeriv)
            (Exec.retainedNodesOfCommits child childCommits) := by
          rw [child.retainedNodesOfCommits_eq_root_cons childCommits]
          simp only [List.map_cons, Exec.Frame.rootDeriv, Exec.Frame.ofRun]
          exact (childIh childCommits).cons_cons _
        have nextFrames : List.Sublist
            ((Exec.descendantFrames next).map Exec.Frame.rootDeriv)
            (Exec.retainedNodesOfCommits next committed) := by
          rw [next.retainedNodesOfCommits_eq_root_cons committed]
          exact (nextIh committed).cons _
        simpa only [List.map_append] using
          childFrames.append nextFrames
      next childDoesNotSettle =>
        rw [next.retainedNodesOfCommits_eq_root_cons committed]
        exact (nextIh committed).cons _

/-- Committed-frame entry roots occur in the retained instruction stream in
the same order.  The sublist relation is the explicit cross-level chronology
link; it does not identify ancestry with global execution order. -/
theorem Exec.committedFrameRoots_sublist_retainedNodes
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    List.Sublist ((Exec.committedFrames run).map Exec.Frame.rootDeriv)
      (Exec.retainedNodes run) := by
  unfold Exec.committedFrames Exec.retainedNodes
  split
  next committed =>
    rw [run.retainedNodesOfCommits_eq_root_cons committed]
    simp only [List.map_cons, Exec.Frame.rootDeriv, Exec.Frame.ofRun]
    exact (Exec.descendantFrameRoots_sublist_retainedNodesOfCommits
      run committed).cons_cons _
  next notCommitted => exact .slnil

/-- An exact reached nonterminal instruction.  The result is the instruction's
own step result, not the enclosing derivation's endpoint.  `slot` retains the
concrete recursive child proof when the instruction entered a child frame. -/
structure Exec.NinstOccurrence (root : Exec.Deriv) : Type where
  node : Exec.Deriv
  instruction : Ninst
  slot : Xlot
  stepResult : Execution
  reached : node ∈ Exec.rawNodes root.exc
  decoded : Ninst.At node.sevm.code node.pc instruction
  filled : slot.Filled
  stepRun : Ninst.StepRun node.pc node.sevm node.devm instruction slot stepResult

/-- The occurrence survives complete root and nested-frame settlement. -/
def Exec.NinstOccurrence.Retained
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root) : Prop :=
  occurrence.node ∈ Exec.retainedNodes root.exc

private theorem List.exists_eq_append_cons_of_mem
    {α : Type} {x : α} {xs : List α} (h : x ∈ xs) :
    ∃ before after, xs = before ++ x :: after := by
  induction xs with
  | nil => simp at h
  | cons head tail ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | htail
      · exact ⟨[], tail, rfl⟩
      · rcases ih htail with ⟨before, after, hsplit⟩
        exact ⟨head :: before, after, by simp [hsplit]⟩

/-- Every occurrence splits the enclosing chronology at its exact proof node. -/
theorem Exec.NinstOccurrence.rawNodes_decomposition
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root) :
    ∃ before after,
      Exec.rawNodes root.exc = before ++ occurrence.node :: after :=
  List.exists_eq_append_cons_of_mem occurrence.reached

/-- A retained occurrence splits the settlement chronology at its exact node. -/
theorem Exec.NinstOccurrence.retainedNodes_decomposition
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root)
    (retained : occurrence.Retained) :
    ∃ before after,
      Exec.retainedNodes root.exc = before ++ occurrence.node :: after :=
  List.exists_eq_append_cons_of_mem retained

/-- Decoding the root of any derivation as a nonterminal instruction recovers
the exact recursive slot and step result for all six `Exec` outcomes. -/
theorem Exec.Deriv.exists_stepRun_of_ninstAt
    (node : Exec.Deriv) {n : Ninst}
    (hat : Ninst.At node.sevm.code node.pc n) :
    ∃ (slot : Xlot) (result : Execution),
      slot.Filled ∧
      Ninst.StepRun node.pc node.sevm node.devm n slot result := by
  rcases node with ⟨pc, sevm, pre, out, run⟩
  have hroot : Evm.step ⟨pc, sevm, pre⟩ =
      Ninst.step ⟨pc, sevm, pre⟩ n := Evm.step_next hat
  cases run with
  | halt hstep =>
      refine ⟨.none, out, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨rfl, rfl⟩
  | cont hstep next =>
      rename_i pc' post
      refine ⟨.none, .ok post, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨rfl, rfl⟩
  | doneErr hstep henter hresume =>
      rename_i frame resume pc' settled err
      refine ⟨.none, .error err, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨settled, RunFrame.of_done henter, hresume.symm⟩
  | doneOk hstep henter hresume next =>
      rename_i frame resume pc' settled post
      refine ⟨.none, .ok post, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨settled, RunFrame.of_done henter, hresume.symm⟩
  | runErr hstep henter child hresume =>
      rename_i frame resume pc' childEvm raw err
      refine ⟨.some ⟨childEvm, raw⟩, .error err, ⟨child⟩, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨frame.settle raw, RunFrame.of_run henter, hresume.symm⟩
  | runOk hstep henter child hresume next =>
      rename_i frame resume pc' childEvm raw post
      refine ⟨.some ⟨childEvm, raw⟩, .ok post, ⟨child⟩, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨frame.settle raw, RunFrame.of_run henter, hresume.symm⟩

/-- Membership plus an exact `.next` decode is complete for the rich
occurrence view. -/
theorem Exec.exists_ninstOccurrence_of_mem_rawNodes
    {root node : Exec.Deriv} {n : Ninst}
    (hreached : node ∈ Exec.rawNodes root.exc)
    (hat : Ninst.At node.sevm.code node.pc n) :
    ∃ occurrence : Exec.NinstOccurrence root,
      occurrence.node = node ∧ occurrence.instruction = n := by
  rcases node.exists_stepRun_of_ninstAt hat with ⟨slot, result, hfilled, hrun⟩
  exact ⟨⟨node, n, slot, result, hreached, hat, hfilled, hrun⟩, rfl, rfl⟩

/-- Soundness and completeness of the occurrence view against exact reached
nodes and nonterminal decoding. -/
theorem Exec.ninstOccurrence_iff_mem_rawNodes
    {root node : Exec.Deriv} {n : Ninst} :
    (∃ occurrence : Exec.NinstOccurrence root,
      occurrence.node = node ∧ occurrence.instruction = n) ↔
      node ∈ Exec.rawNodes root.exc ∧
        Ninst.At node.sevm.code node.pc n := by
  constructor
  · rintro ⟨occurrence, rfl, rfl⟩
    exact ⟨occurrence.reached, occurrence.decoded⟩
  · rintro ⟨hreached, hat⟩
    exact Exec.exists_ninstOccurrence_of_mem_rawNodes hreached hat

/-! ## Frame-entry-free derivations

`Exec` spawns a child frame only at `runErr` and `runOk`, and `Evm.step`
reaches `.spawn` only through `Ninst.exec`.  Excluding every `Xinst` at every
reached node therefore collapses the raw frame traversal to the outer root.
The exclusion has to cover the whole `Xinst` family — `create`, `call`,
`callcode`, `delcall`, `create2`, `statcall` — because any one of them alone
produces a descendant. -/

/-- A derivation whose reached nodes never decode an executable instruction
enters no child frame.  Node level, so the recursion carries no occurrence
transport. -/
theorem Exec.rawFrameDescendants_eq_nil_of_no_xinstAt
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (childless : ∀ node ∈ Exec.rawNodes run, ∀ x : Xinst,
      ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    Exec.rawFrameDescendants run = [] := by
  induction run with
  | halt => simp [Exec.rawFrameDescendants]
  | cont hstep next ih =>
      simp only [Exec.rawFrameDescendants]
      refine ih fun node reached => ?_
      exact childless node (by simp [Exec.rawNodes, reached])
  | doneErr => simp [Exec.rawFrameDescendants]
  | doneOk hstep henter hresume next ih =>
      simp only [Exec.rawFrameDescendants]
      refine ih fun node reached => ?_
      exact childless node (by simp [Exec.rawNodes, reached])
  | runErr hstep henter child hresume childIh =>
      rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
      exact absurd decoded
        (childless _ (Exec.mem_rawNodes_self _) x)
  | runOk hstep henter child hresume next childIh nextIh =>
      rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
      exact absurd decoded
        (childless _ (Exec.mem_rawNodes_self _) x)

/-- Occurrence-facing form: no occurrence of the root decodes a frame-entering
instruction, so the root enters no child frame. -/
theorem Exec.rawFrameDescendants_eq_nil_of_no_execOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (childless : ∀ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      ∀ x : Xinst, occurrence.instruction ≠ .exec x) :
    Exec.rawFrameDescendants run = [] := by
  refine run.rawFrameDescendants_eq_nil_of_no_xinstAt ?_
  intro node reached x decoded
  rcases Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv)) reached decoded with
    ⟨occurrence, -, instructionEq⟩
  exact childless occurrence x instructionEq

/-- The raw frame traversal of a frame-entry-free derivation is the singleton
outer root.  This is the form that discharges a `Exec.rawFrameRoots`
membership premise by `List.mem_singleton`. -/
theorem Exec.rawFrameRoots_eq_singleton_of_no_execOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (childless : ∀ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      ∀ x : Xinst, occurrence.instruction ≠ .exec x) :
    Exec.rawFrameRoots run = [⟨pc, sevm, pre, out, run⟩] := by
  rw [Exec.rawFrameRoots,
    Exec.rawFrameDescendants_eq_nil_of_no_execOccurrence run childless]

/-- Every selected raw frame root of a frame-entry-free derivation is the
outer root itself. -/
theorem Exec.eq_of_mem_rawFrameRoots_of_no_execOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {frameRoot : Exec.Deriv}
    (childless : ∀ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      ∀ x : Xinst, occurrence.instruction ≠ .exec x)
    (selected : frameRoot ∈ Exec.rawFrameRoots run) :
    frameRoot = ⟨pc, sevm, pre, out, run⟩ := by
  rw [Exec.rawFrameRoots_eq_singleton_of_no_execOccurrence run childless,
    List.mem_singleton] at selected
  exact selected

/-- A successful persistent write occurrence.  There is intentionally no
old-value/new-value inequality: a successful no-op `SSTORE` is retained. -/
structure Exec.SuccessfulSstoreOccurrence (root : Exec.Deriv) : Type where
  occurrence : Exec.NinstOccurrence root
  instruction_eq : occurrence.instruction = .reg .sstore
  stepPost : Devm
  stepSuccess : occurrence.stepResult = .ok stepPost
  key : B256
  value : B256
  popped : Stack.Pop [key, value] occurrence.node.devm.stack stepPost.stack

/-- A successful SSTORE whose effects survive complete settlement. -/
def Exec.SuccessfulSstoreOccurrence.Retained
    {root : Exec.Deriv}
    (write : Exec.SuccessfulSstoreOccurrence root) : Prop :=
  write.occurrence.Retained

/-! ## Retained storage replay -/

/-- Proof-free data projected from one successful SSTORE.  The exact proof
node is retained so soundness can reconstruct the public occurrence witness. -/
structure Exec.StorageWrite where
  node : Exec.Deriv
  owner : Adr
  key : B256
  value : B256

@[ext] theorem Exec.StorageWrite.ext
    {left right : Exec.StorageWrite}
    (node : left.node = right.node)
    (owner : left.owner = right.owner)
    (key : left.key = right.key)
    (value : left.value = right.value) : left = right := by
  cases left
  cases right
  simp_all

/-- Executably recognize a successful SSTORE driver node and project its raw
stack key/value.  Terminal and spawning nodes cannot be successful SSTOREs. -/
def Exec.Deriv.successfulSstore? (node : Exec.Deriv) : Option Exec.StorageWrite :=
  match node.exc with
  | .cont _ _ =>
      match Evm.getInst ⟨node.pc, node.sevm, node.devm⟩, node.devm.stack with
      | some (.next (.reg .sstore)), key :: value :: _ =>
          some { node, owner := node.sevm.currentTarget, key, value }
      | _, _ => none
  | _ => none

/-- Successful retained SSTORE events in the canonical global chronology. -/
def Exec.retainedStorageWrites
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.StorageWrite :=
  (Exec.retainedNodes run).filterMap Exec.Deriv.successfulSstore?

/-- Project the data fields of an exact successful SSTORE occurrence. -/
def Exec.SuccessfulSstoreOccurrence.storageWrite
    {root : Exec.Deriv}
    (write : Exec.SuccessfulSstoreOccurrence root) : Exec.StorageWrite :=
  { node := write.occurrence.node
    owner := write.occurrence.node.sevm.currentTarget
    key := write.key
    value := write.value }

/-- Whether an event writes the selected persistent cell. -/
def Exec.StorageWrite.matches
    (write : Exec.StorageWrite) (owner : Adr) (key : B256) : Bool :=
  write.owner == owner && write.key == key

@[simp] theorem Exec.StorageWrite.matches_eq_true
    {write : Exec.StorageWrite} {owner : Adr} {key : B256} :
    write.matches owner key = true ↔
      write.owner = owner ∧ write.key = key := by
  simp [Exec.StorageWrite.matches]

/-- Replay the selected storage word through chronological successful writes. -/
def Exec.StorageWrite.replayCell
    (owner : Adr) (key : B256) (initial : B256) :
    List Exec.StorageWrite → B256 :=
  fun writes => writes.foldl (fun current write =>
    if write.matches owner key then write.value else current) initial

private theorem Exec.StorageWrite.foldlCell_append
    {owner : Adr} {key : B256} (initial : B256)
    (left right : List Exec.StorageWrite) :
    (left ++ right).foldl
        (fun current write =>
          if write.matches owner key then write.value else current) initial =
      right.foldl
        (fun current write =>
          if write.matches owner key then write.value else current)
        (left.foldl
          (fun current write =>
            if write.matches owner key then write.value else current) initial) := by
  simp [List.foldl_append]

private theorem Exec.StorageWrite.foldlCell_eq_of_none
    {owner : Adr} {key : B256} {writes : List Exec.StorageWrite}
    (initial : B256)
    (none : ∀ write ∈ writes, write.matches owner key ≠ true) :
    writes.foldl
        (fun current write =>
          if write.matches owner key then write.value else current) initial =
      initial := by
  induction writes generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [if_neg (none head (by simp))]
      exact ih initial (by
        intro write member
        exact none write (by simp [member]))

private theorem Exec.StorageWrite.exists_last_matching
    {owner : Adr} {key : B256} {writes : List Exec.StorageWrite}
    (existsMatch : ∃ write ∈ writes, write.matches owner key = true) :
    ∃ before write after,
      writes = before ++ write :: after ∧
      write.matches owner key = true ∧
      ∀ later ∈ after, later.matches owner key ≠ true := by
  induction writes with
  | nil => simp at existsMatch
  | cons head tail ih =>
      by_cases tailMatch : ∃ write ∈ tail,
          write.matches owner key = true
      · rcases ih tailMatch with ⟨before, write, after, hsplit,
          hmatch, hlast⟩
        exact ⟨head :: before, write, after, by simp [hsplit], hmatch, hlast⟩
      · have headMatch : head.matches owner key = true := by
          rcases existsMatch with ⟨write, member, hmatch⟩
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact hmatch
          · exact (tailMatch ⟨write, member, hmatch⟩).elim
        exact ⟨[], head, tail, rfl, headMatch, by
          intro later member hmatch
          exact tailMatch ⟨later, member, hmatch⟩⟩

private theorem Exec.StorageWrite.last_value_eq_foldlCell
    {owner : Adr} {key : B256} {writes : List Exec.StorageWrite}
    {before after : List Exec.StorageWrite} {write : Exec.StorageWrite}
    (split : writes = before ++ write :: after)
    (matchWrite : write.matches owner key = true)
    (last : ∀ later ∈ after, later.matches owner key ≠ true)
    (initial : B256) :
    writes.foldl
        (fun current event =>
          if event.matches owner key then event.value else current) initial =
      write.value := by
  subst writes
  rw [Exec.StorageWrite.foldlCell_append]
  simp only [List.foldl_cons, matchWrite, if_true]
  exact Exec.StorageWrite.foldlCell_eq_of_none write.value last

/-- Pointwise storage effect of a chronological successful-write list. -/
def Exec.StorageReplay
    (pre post : Devm) (writes : List Exec.StorageWrite) : Prop :=
  ∀ owner key,
    (Devm.getStor post owner).get key =
      Exec.StorageWrite.replayCell owner key
        ((Devm.getStor pre owner).get key) writes

theorem Exec.StorageReplay.refl (state : Devm) :
    Exec.StorageReplay state state [] := by
  intro owner key
  rfl

theorem Exec.StorageReplay.of_getStor_eq
    {pre post : Devm} (equal : Devm.getStor post = Devm.getStor pre) :
    Exec.StorageReplay pre post [] := by
  intro owner key
  simpa [Exec.StorageWrite.replayCell] using
    congrArg (fun storage : Stor => storage.get key) (congrFun equal owner)

theorem Exec.StorageReplay.append
    {pre middle post : Devm}
    {left right : List Exec.StorageWrite}
    (head : Exec.StorageReplay pre middle left)
    (tail : Exec.StorageReplay middle post right) :
    Exec.StorageReplay pre post (left ++ right) := by
  intro owner key
  rw [tail owner key, head owner key]
  unfold Exec.StorageWrite.replayCell
  exact (Exec.StorageWrite.foldlCell_append _ left right).symm

/-- Message-entry value transfer changes balances but not persistent storage. -/
theorem benvAfterTransfer_getStor_eq
    {msg : Msg} {benv : Benv}
    (transfer : msg.benvAfterTransfer = .ok benv) :
    benv.state.getStor = msg.benv.state.getStor := by
  funext owner
  by_cases enabled : msg.shouldTransferValue = true
  · rcases of_benvAfterTransfer enabled transfer with
      ⟨middle, sub, rfl⟩
    exact (of_state_transfer_fields sub).1 owner
  · rw [of_benvAfterTransfer_no enabled transfer]

/-- Settlement-aware replay transport for a concrete CALL message body. -/
theorem ProcessMessage.storageReplay_of_body
    {msg : Msg} {post parent : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {writes : List Exec.StorageWrite}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (parentState : parent.state = msg.benv.state)
    (body : ∀ committed : Execution.commits out = true,
      Exec.StorageReplay pre (Execution.committedPost out committed) writes) :
    Exec.StorageReplay parent post
      (if Frame.settlementCommits (Frame.ofCall msg) out = true
       then writes else []) := by
  by_cases settles : Frame.settlementCommits (Frame.ofCall msg) out = true
  · rw [if_pos settles]
    have committed := Frame.raw_commits_of_settlementCommits settles
    have enter : (Frame.ofCall msg).enter = .run ⟨pc, sevm, pre⟩ :=
      (RunFrame.some_inv process).1
    rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
    simp only [Frame.ofCall] at transfer evmEq
    have preState : pre.state = benv.state := by
      exact congrArg (fun evm : Evm => evm.dyna.state) evmEq
    have prefixEq : Devm.getStor pre = Devm.getStor parent := by
      funext owner
      change pre.state.getStor owner = parent.state.getStor owner
      rw [preState, parentState, benvAfterTransfer_getStor_eq transfer]
    have postState : post.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost process committed
    have suffixEq : Devm.getStor post =
        Devm.getStor (Execution.committedPost out committed) := by
      funext owner
      exact congrArg (fun state : State => state.getStor owner) postState
    simpa only [List.nil_append, List.append_nil] using
      (Exec.StorageReplay.of_getStor_eq prefixEq).append
        ((body committed).append (Exec.StorageReplay.of_getStor_eq suffixEq))
  · rw [if_neg settles]
    have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notNone : post.error.isNone ≠ true := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        exact clean
      cases errorEq : post.error <;> simp_all
    have rollback := (ProcessMessage.rollback_of_error process postError).1
    apply Exec.StorageReplay.of_getStor_eq
    funext owner
    change post.state.getStor owner = parent.state.getStor owner
    rw [rollback, parentState]

/-- Clean CREATE code-deposit settlement preserves the constructor body's
persistent storage at every address. -/
theorem ProcessCreateMessage.ok_getStor_eq_inner_of_clean
    {msg : Msg} {slot : Xlot} {post : Devm}
    (process : ProcessCreateMessage msg slot (.ok post))
    (clean : post.error.isSome = false) :
    ∃ inner : Devm,
      ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
      Devm.getStor post = Devm.getStor inner ∧
      inner.error.isSome = false := by
  rcases ProcessCreateMessage.iff_processMessage.mp process with
    ⟨result, innerProcess, settled⟩
  cases result with
  | error error => simp [processCreateMessage.settle] at settled
  | ok inner =>
      unfold processCreateMessage.settle at settled
      simp only [bind, Except.bind] at settled
      by_cases innerClean : inner.error.isNone = true
      · rw [if_pos innerClean] at settled
        cases charge : processCreateMessage.chargeCodeGas
            msg.benv.stat.rules inner with
        | error error =>
            rw [charge] at settled
            rcases error with ⟨error, charged⟩
            cases error with
            | halt reason =>
                have eq := Except.ok.inj settled
                rw [eq] at clean
                simp [processCreateMessage.exceptionalHalt,
                  Devm.error, Devm.setMeta] at clean
            | revert => cases settled
            | crypto reason => cases settled
            | internal reason => cases settled
        | ok charged =>
            rw [charge] at settled
            have eq := Except.ok.inj settled
            refine ⟨inner, innerProcess, ?_, ?_⟩
            · funext owner
              calc
                Devm.getStor post owner =
                    Devm.getStor
                      (charged.setCode msg.currentTarget
                        ⟨⟨charged.output⟩⟩) owner := by rw [eq]
                _ = Devm.getStor charged owner := by
                  change ((charged.state.setCode msg.currentTarget
                    ⟨⟨charged.output⟩⟩).get owner).stor = _
                  exact State.setCode_get_stor
                _ = Devm.getStor inner owner := by
                  exact congrArg (fun state : State => state.getStor owner)
                    (chargeCodeGas_state_ok charge)
            · cases errorEq : inner.error <;> simp_all
      · rw [if_neg innerClean] at settled
        have eq := Except.ok.inj settled
        rw [eq] at clean
        change (inner.rollback msg.benv.state
          msg.tenv.transientStorage).error.isSome = false at clean
        change inner.error.isSome = false at clean
        have innerNone : inner.error.isNone = true := by
          cases errorEq : inner.error <;> simp_all
        exact (innerClean innerNone).elim

/-- CREATE's fresh-account preparation is storage-silent when the target was
already storage-empty, including at the target address itself. -/
theorem processCreateMessage_msg_getStor_eq_of_empty
    {msg : Msg}
    (empty : msg.benv.state.getStor msg.currentTarget = .empty) :
    (processCreateMessage.msg msg).benv.state.getStor =
      msg.benv.state.getStor := by
  funext owner
  by_cases target : msg.currentTarget = owner
  · subst owner
    dsimp [processCreateMessage.msg, Msg.withBenv, addCreatedAccount,
      Benv.setStor, Benv.incrNonce, State.getStor]
    rw [State.incrNonce_get_stor]
    unfold State.setStor
    rw [State.get_set_self]
    exact empty.symm
  · dsimp [processCreateMessage.msg, Msg.withBenv, addCreatedAccount,
      Benv.setStor, Benv.incrNonce, State.getStor]
    rw [State.incrNonce_get_stor, State.setStor_get_stor_ne target]

/-- Settlement-aware replay transport for a concrete CREATE constructor.  The
full CREATE settlement bit, rather than raw constructor success, decides
whether constructor writes survive code deposit. -/
theorem ProcessCreateMessage.storageReplay_of_body
    {msg : Msg} {post parent : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {writes : List Exec.StorageWrite}
    (process : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (parentState : parent.state = msg.benv.state)
    (fresh : Devm.getStor parent msg.currentTarget = .empty)
    (body : ∀ committed : Execution.commits out = true,
      Exec.StorageReplay pre (Execution.committedPost out committed) writes) :
    Exec.StorageReplay parent post
      (if Frame.settlementCommits (Frame.ofCreate msg) out = true
       then writes else []) := by
  by_cases settles : Frame.settlementCommits (Frame.ofCreate msg) out = true
  · rw [if_pos settles]
    have clean : post.error.isSome = false := by
      have settledEq := (RunFrame.some_inv process).2
      unfold Frame.settlementCommits at settles
      rw [← settledEq] at settles
      cases errorEq : post.error <;> simp_all
    rcases ProcessCreateMessage.ok_getStor_eq_inner_of_clean process clean with
      ⟨inner, innerProcess, postEq, innerClean⟩
    let prepared : Devm :=
      parent.withState (processCreateMessage.msg msg).benv.state
    have preparedEq : Devm.getStor prepared = Devm.getStor parent := by
      rw [show Devm.getStor prepared =
          (processCreateMessage.msg msg).benv.state.getStor from rfl]
      rw [processCreateMessage_msg_getStor_eq_of_empty (by
        rw [← parentState]
        exact fresh)]
      funext owner
      change msg.benv.state.getStor owner = parent.state.getStor owner
      rw [← parentState]
    have innerSettles :
        Frame.settlementCommits
          (Frame.ofCall (processCreateMessage.msg msg)) out = true := by
      have innerEq := (RunFrame.some_inv innerProcess).2
      unfold Frame.settlementCommits
      rw [← innerEq]
      cases errorEq : inner.error <;> simp_all
    have innerReplay := ProcessMessage.storageReplay_of_body
      innerProcess (parent := prepared) rfl body
    rw [if_pos innerSettles] at innerReplay
    simpa only [List.nil_append, List.append_nil] using
      (Exec.StorageReplay.of_getStor_eq preparedEq).append
        (innerReplay.append (Exec.StorageReplay.of_getStor_eq postEq))
  · rw [if_neg settles]
    have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notClean : post.error.isSome ≠ false := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        cases errorEq : post.error <;> simp_all
      cases errorEq : post.error <;> simp_all
    have rollback := ProcessCreateMessage.rollback_of_error process postError
    apply Exec.StorageReplay.of_getStor_eq
    funext owner
    change post.state.getStor owner = parent.state.getStor owner
    rw [rollback, parentState]

/-- Replay transport through the concrete recursive slot of a generic CALL. -/
theorem GenericCall.storageReplay_some_of_body
    {sevm : Sevm} {pre post : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray}
    {disablePrecompiles : Bool}
    {pc : Nat} {childSevm : Sevm} {childPre : Devm}
    {out : Execution} {writes : List Exec.StorageWrite}
    (run : GenericCall sevm pre gas value caller target codeAddress stv
      isStatic ii is oi os code disablePrecompiles
      (.some ⟨⟨pc, childSevm, childPre⟩, out⟩) (.ok post))
    (body : ∀ committed : Execution.commits out = true,
      Exec.StorageReplay childPre
        (Execution.committedPost out committed) writes) :
    Exec.StorageReplay pre post
      (if Frame.settlementCommits
          (Frame.ofCall
            (callMsg sevm (pre.withReturnData []) gas value caller target
              codeAddress stv isStatic ((pre.memory.read ii is).1) code
              disablePrecompiles)) out = true
       then writes else []) := by
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.1
  · cases run.1
  · obtain ⟨result, process, resume⟩ := run
    rcases result with error | child
    · cases Resume.call_run_error resume.symm
    have childState : post.state = child.state :=
      Resume.call_state resume.symm
    let callPre := pre.withReturnData []
    let msg := callMsg sevm callPre gas value caller target codeAddress stv
      isStatic ((callPre.memory.read ii is).1) code disablePrecompiles
    have process' : ProcessMessage msg
        (.some ⟨⟨pc, childSevm, childPre⟩, out⟩) (.ok child) := by
      simpa only [ProcessMessage, msg, callPre, Mem.read] using process
    have replay := ProcessMessage.storageReplay_of_body
      process' (parent := callPre) rfl body
    have prefixEq : Devm.getStor callPre = Devm.getStor pre := rfl
    have suffixEq : Devm.getStor post = Devm.getStor child := by
      funext owner
      exact congrArg (fun state : State => state.getStor owner) childState
    have memoryEq : callPre.memory = pre.memory := rfl
    dsimp only [msg] at replay
    rw [memoryEq] at replay
    dsimp only [callPre] at replay
    convert
      (Exec.StorageReplay.of_getStor_eq prefixEq).append
        (replay.append (Exec.StorageReplay.of_getStor_eq suffixEq)) using 1
    by_cases retain : Frame.settlementCommits
        (Frame.ofCall
          (callMsg sevm (pre.withReturnData []) gas value caller target
            codeAddress stv isStatic ((pre.memory.read ii is).1) code
            disablePrecompiles)) out = true <;>
      simp [retain]

/-- Replay transport through the concrete recursive slot of a generic CREATE,
including pruning on failed code deposit. -/
theorem GenericCreate.storageReplay_some_of_body
    {sevm : Sevm} {pre post : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {pc : Nat} {childSevm : Sevm} {childPre : Devm}
    {out : Execution} {writes : List Exec.StorageWrite}
    (run : GenericCreate sevm pre endowment newAddress mi ms
      (.some ⟨⟨pc, childSevm, childPre⟩, out⟩) (.ok post))
    (body : ∀ committed : Execution.commits out = true,
      Exec.StorageReplay childPre
        (Execution.committedPost out committed) writes) :
    Exec.StorageReplay pre post
      (if Frame.settlementCommits
          (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))) out = true
       then writes else []) := by
  obtain ⟨frame, resume, spawn, -, -⟩ := XStep.Run.some_inv run
  have targetEmpty : Devm.getStor pre newAddress = .empty :=
    genericCreate_step_spawn_getStor_empty spawn
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  all_goals try
    (have slotEq : (some ⟨⟨pc, childSevm, childPre⟩, out⟩ : Xlot) = none :=
      run.1
     cases slotEq)
  obtain ⟨result, process, resumeRun⟩ := run
  cases result with
  | error error =>
      simp [Resume.run, liftToExecution] at resumeRun
  | ok settled =>
      let createPre :=
        addAccessedAddress
          (((pre.withGasLeft
              (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress
      let msg := createMsg sevm createPre (except64th pre.gasLeft)
        endowment newAddress ((pre.memory.read mi ms).1)
      have process' : ProcessCreateMessage msg
          (.some ⟨⟨pc, childSevm, childPre⟩, out⟩) (.ok settled) := by
        simpa only [ProcessCreateMessage, msg, createPre, Mem.read] using
          process
      have prefixEq : Devm.getStor createPre = Devm.getStor pre := by
        funext owner
        have stateEq : createPre.state =
            pre.state.incrNonce sevm.currentTarget := by
          rfl
        change createPre.state.getStor owner = pre.state.getStor owner
        rw [stateEq]
        exact State.incrNonce_get_stor
      have replay := ProcessCreateMessage.storageReplay_of_body
        process' (parent := createPre) rfl (by
          rw [prefixEq]
          exact targetEmpty) body
      have settledState : post.state = settled.state :=
        Resume.create_state resumeRun.symm
      have suffixEq : Devm.getStor post = Devm.getStor settled := by
        funext owner
        exact congrArg (fun state : State => state.getStor owner) settledState
      dsimp only [msg] at replay
      dsimp only [createPre] at replay
      convert
        (Exec.StorageReplay.of_getStor_eq prefixEq).append
          (replay.append (Exec.StorageReplay.of_getStor_eq suffixEq)) using 1
      by_cases retain : Frame.settlementCommits
          (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))) out = true <;>
        simp [retain]

/-- Contract-neutral recursive executable-instruction transport. -/
theorem Xinst.storageReplay_some_of_body
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume}
    {pc : Nat} {childSevm : Sevm} {childPre : Devm}
    {out : Execution}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    {writes : List Exec.StorageWrite}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame
      (.some ⟨⟨pc, childSevm, childPre⟩, out⟩) result)
    (resumeRun : resume.run result = .ok post)
    (body : ∀ committed : Execution.commits out = true,
      Exec.StorageReplay childPre
        (Execution.committedPost out committed) writes) :
    Exec.StorageReplay pre post
      (if Frame.settlementCommits frame out = true then writes else []) := by
  rcases Xinst.step_shape sevm pre x with
    ⟨execution, shape, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, rfl⟩
    have run : GenericCreate sevm d endowment newAddress mi ms
        (.some ⟨⟨pc, childSevm, childPre⟩, out⟩) (.ok post) := by
      unfold GenericCreate XStep.Run
      rw [spawn]
      exact ⟨result, frameRun, resumeRun.symm⟩
    have replay := GenericCreate.storageReplay_some_of_body run body
    simpa only [List.nil_append] using
      (Exec.StorageReplay.of_getStor_eq
        (funext hprefix.getStor).symm).append replay
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    have run : GenericCall sevm d gas value caller target codeAddress stv
        isStatic ii isz oi osz code disablePrecompiles
        (.some ⟨⟨pc, childSevm, childPre⟩, out⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [spawn]
      exact ⟨result, frameRun, resumeRun.symm⟩
    have replay := GenericCall.storageReplay_some_of_body run body
    simpa only [List.nil_append] using
      (Exec.StorageReplay.of_getStor_eq
        (funext hprefix.getStor).symm).append replay

/-- The storage owner is the executing frame's current target. -/
def Exec.SuccessfulSstoreOccurrence.storageOwner
    {root : Exec.Deriv} (write : Exec.SuccessfulSstoreOccurrence root) : Adr :=
  write.occurrence.node.sevm.currentTarget

/-- Refine a successful decoded `SSTORE` without discarding no-op writes. -/
theorem Exec.NinstOccurrence.toSuccessfulSstore
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root)
    (hinstruction : occurrence.instruction = .reg .sstore)
    {post : Devm} (hsuccess : occurrence.stepResult = .ok post) :
    ∃ write : Exec.SuccessfulSstoreOccurrence root,
      write.occurrence = occurrence := by
  have hrun : Ninst.Run occurrence.node.sevm occurrence.node.devm
      (.reg .sstore) post := by
    refine ⟨occurrence.slot, occurrence.filled, occurrence.node.pc, ?_⟩
    simpa only [hinstruction, hsuccess] using occurrence.stepRun
  rcases of_run_sstore hrun with ⟨key, value, hpop⟩
  exact ⟨⟨occurrence, hinstruction, post, hsuccess, key, value, hpop⟩, rfl⟩

/-- The successful occurrence performs the exact key/value update it records. -/
theorem Exec.SuccessfulSstoreOccurrence.storage_update
    {root : Exec.Deriv} (write : Exec.SuccessfulSstoreOccurrence root) :
    Devm.getStor write.stepPost write.storageOwner =
      (Devm.getStor write.occurrence.node.devm write.storageOwner).set
        write.key write.value := by
  have hrun : Ninst.Run write.occurrence.node.sevm write.occurrence.node.devm
      (.reg .sstore) write.stepPost := by
    refine ⟨write.occurrence.slot, write.occurrence.filled,
      write.occurrence.node.pc, ?_⟩
    simpa only [write.instruction_eq, write.stepSuccess] using
      write.occurrence.stepRun
  exact sstore_getStor_set hrun (pref_of_split write.popped)

/-- The executable event projection is sound for every retained node. -/
theorem Exec.Deriv.successfulSstore?_sound
    {root node : Exec.Deriv} {event : Exec.StorageWrite}
    (retained : node ∈ Exec.retainedNodes root.exc)
    (found : node.successfulSstore? = some event) :
    ∃ write : Exec.SuccessfulSstoreOccurrence root,
      write.Retained ∧ write.storageWrite = event := by
  have raw : node ∈ Exec.rawNodes root.exc :=
    (Exec.retainedNodes_sublist_rawNodes root.exc).subset retained
  rcases node with ⟨pc, sevm, pre, out, run⟩
  cases run with
  | halt hstep => simp [Exec.Deriv.successfulSstore?] at found
  | doneErr hstep henter hresume =>
      simp [Exec.Deriv.successfulSstore?] at found
  | doneOk hstep henter hresume next =>
      simp [Exec.Deriv.successfulSstore?] at found
  | runErr hstep henter child hresume =>
      simp [Exec.Deriv.successfulSstore?] at found
  | runOk hstep henter child hresume next =>
      simp [Exec.Deriv.successfulSstore?] at found
  | cont hstep next =>
      cases hget : Evm.getInst ⟨pc, sevm, pre⟩ with
      | none => simp [Exec.Deriv.successfulSstore?, hget] at found
      | some instruction =>
          cases instruction with
          | jump jumpInst => simp [Exec.Deriv.successfulSstore?, hget] at found
          | last last => simp [Exec.Deriv.successfulSstore?, hget] at found
          | next instruction =>
              cases instruction with
              | exec exec =>
                  simp [Exec.Deriv.successfulSstore?, hget] at found
              | push bytes size =>
                  simp [Exec.Deriv.successfulSstore?, hget] at found
              | reg regular =>
                  cases regular <;>
                    try simp [Exec.Deriv.successfulSstore?, hget] at found
                  cases hstack : pre.stack with
                  | nil =>
                      simp [hstack] at found
                  | cons key rest =>
                      cases rest with
                      | nil =>
                          simp [hstack] at found
                      | cons value tail =>
                          simp [hstack] at found
                          subst event
                          let occurrence : Exec.NinstOccurrence root :=
                            { node := ⟨pc, sevm, pre, out, .cont hstep next⟩
                              instruction := .reg .sstore
                              slot := .none
                              stepResult := .ok _
                              reached := raw
                              decoded := hget
                              filled := trivial
                              stepRun := by
                                unfold Ninst.StepRun
                                rw [← Evm.step_next hget, hstep]
                                exact ⟨rfl, rfl⟩ }
                          rcases occurrence.toSuccessfulSstore rfl rfl with
                            ⟨write, hwrite⟩
                          refine ⟨write, ?_, ?_⟩
                          · unfold Exec.SuccessfulSstoreOccurrence.Retained Exec.NinstOccurrence.Retained
                            rw [hwrite]
                            exact retained
                          · have known : [key, value] <<+ pre.stack := by
                              rw [hstack]
                              exact ⟨tail, rfl⟩
                            have popped := write.popped
                            rw [hwrite] at popped
                            rcases of_cons_cons_pref_of_cons_cons_pref known
                                (pref_of_split popped) with
                              ⟨hkey, hvalue, remainder⟩
                            ext
                            · unfold Exec.SuccessfulSstoreOccurrence.storageWrite
                              rw [hwrite]
                            · unfold Exec.SuccessfulSstoreOccurrence.storageWrite
                              rw [hwrite]
                            · simpa [Exec.SuccessfulSstoreOccurrence.storageWrite]
                                using hkey.symm
                            · simpa [Exec.SuccessfulSstoreOccurrence.storageWrite]
                                using hvalue.symm

/-- Every retained projected event has an exact retained SSTORE occurrence. -/
theorem Exec.exists_successfulSstore_of_mem_retainedStorageWrites
    {root : Exec.Deriv} {event : Exec.StorageWrite}
    (member : event ∈ Exec.retainedStorageWrites root.exc) :
    ∃ write : Exec.SuccessfulSstoreOccurrence root,
      write.Retained ∧ write.storageWrite = event := by
  simp only [Exec.retainedStorageWrites, List.mem_filterMap] at member
  rcases member with ⟨node, nodeMember, found⟩
  exact Exec.Deriv.successfulSstore?_sound (root := root) (node := node)
    nodeMember found

/-- The selected write is the last retained successful SSTORE to its exact
storage owner and raw key.  A later no-op write therefore supersedes an
earlier value-changing write. -/
def Exec.SuccessfulSstoreOccurrence.IsLastRetained
    {root : Exec.Deriv}
    (write : Exec.SuccessfulSstoreOccurrence root) : Prop :=
  ∃ before after,
    Exec.retainedStorageWrites root.exc =
      before ++ write.storageWrite :: after ∧
    ∀ later ∈ after,
      ¬ (later.owner = write.storageOwner ∧ later.key = write.key)

private theorem Exec.StorageWrite.exists_match_of_foldl_ne
    {owner : Adr} {key initial : B256}
    {writes : List Exec.StorageWrite}
    (changed : writes.foldl
        (fun current write =>
          if write.matches owner key then write.value else current) initial ≠
      initial) :
    ∃ write ∈ writes, write.matches owner key = true := by
  by_contra none
  push Not at none
  exact changed (Exec.StorageWrite.foldlCell_eq_of_none initial none)

/-- Pure chronological last-writer selection from a replay equation. -/
private theorem Exec.exists_lastRetainedSstore_of_replay
    {root : Exec.Deriv} {owner : Adr} {key initial final : B256}
    (replay : final = Exec.StorageWrite.replayCell owner key initial
      (Exec.retainedStorageWrites root.exc))
    (changed : initial ≠ final) :
    ∃ write : Exec.SuccessfulSstoreOccurrence root,
      write.Retained ∧
      write.storageOwner = owner ∧
      write.key = key ∧
      write.value = final ∧
      write.IsLastRetained := by
  have foldChanged :
      (Exec.retainedStorageWrites root.exc).foldl
          (fun current write =>
            if write.matches owner key then write.value else current) initial ≠
        initial := by
    intro equal
    apply changed
    rw [replay]
    exact equal.symm
  rcases Exec.StorageWrite.exists_match_of_foldl_ne foldChanged with
    ⟨event, member, matchEvent⟩
  rcases Exec.StorageWrite.exists_last_matching
      (writes := Exec.retainedStorageWrites root.exc)
      ⟨event, member, matchEvent⟩ with
    ⟨before, lastEvent, after, split, lastMatch, maximal⟩
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (event := lastEvent) (by rw [split]; simp) with
    ⟨write, retained, eventEq⟩
  have identities := Exec.StorageWrite.matches_eq_true.mp lastMatch
  have valueEq : write.value = final := by
    rw [replay]
    unfold Exec.StorageWrite.replayCell
    rw [Exec.StorageWrite.last_value_eq_foldlCell split lastMatch maximal]
    simpa [Exec.SuccessfulSstoreOccurrence.storageWrite] using
      congrArg Exec.StorageWrite.value eventEq
  refine ⟨write, retained, ?_, ?_, valueEq, ?_⟩
  · change write.occurrence.node.sevm.currentTarget = owner
    exact (congrArg Exec.StorageWrite.owner eventEq).trans identities.1
  · simpa [Exec.SuccessfulSstoreOccurrence.storageWrite] using
      (congrArg Exec.StorageWrite.key eventEq).trans identities.2
  · refine ⟨before, after, ?_, ?_⟩
    · rw [eventEq]
      exact split
    · intro later laterMember same
      apply maximal later laterMember
      apply Exec.StorageWrite.matches_eq_true.mpr
      change later.owner = write.occurrence.node.sevm.currentTarget ∧
        later.key = write.key at same
      exact ⟨same.1.trans
        ((congrArg Exec.StorageWrite.owner eventEq).trans identities.1),
        same.2.trans
          ((congrArg Exec.StorageWrite.key eventEq).trans identities.2)⟩

/-! ## Semantic replay through execution -/

/-- One successful nonterminal driver step has exactly the storage effect
recognized by `successfulSstore?`: either one raw SSTORE event or none. -/
private theorem Exec.storageReplay_cont_head
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (next : Exec pc' sevm post out) :
    Exec.StorageReplay pre post
      ([⟨pc, sevm, pre, out, Exec.cont step next⟩].filterMap
        Exec.Deriv.successfulSstore?) := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error =>
              rw [jumpEq] at step
              cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumpEq] at step
              cases step
              have frame :=
                Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumpEq] at frame
              simpa [Exec.Deriv.successfulSstore?, decoded] using
                Exec.StorageReplay.of_getStor_eq (funext frame.getStor).symm
      | last last =>
          rw [Evm.step_last decoded] at step
          cases step
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction =
              .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + instruction.size :=
            Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases instruction with
          | push bytes bound =>
              have equal : Devm.getStor pre = Devm.getStor post :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (show Ninst.Run sevm pre (.push bytes bound) post from
                    ⟨.none, trivial, pc, nrun⟩)
              simpa [Exec.Deriv.successfulSstore?, decoded] using
                Exec.StorageReplay.of_getStor_eq equal.symm
          | exec executable =>
              have xrun : Xinst.Run sevm pre executable .none (.ok post) :=
                XStep.run_toStep.mp nrun
              simpa [Exec.Deriv.successfulSstore?, decoded] using
                Exec.StorageReplay.of_getStor_eq
                  (Xinst.none_getStor_eq xrun)
          | reg regular =>
              have rrun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post := by
                have equal : (.ok post : Execution) =
                    Rinst.run ⟨pc, sevm, pre⟩ regular := by
                  simpa [Ninst.StepRun, Ninst.step_reg,
                    Step.run_ofExecution] using nrun
                exact equal.symm
              by_cases store : regular = .sstore
              · subst regular
                have sstoreRun : Ninst.Run sevm pre Ninst.sstore post :=
                  ⟨.none, trivial, pc, nrun⟩
                cases stackEq : pre.stack with
                | nil =>
                    rcases of_run_sstore sstoreRun with ⟨key, value, popped⟩
                    have pref := pref_of_split popped
                    rcases pref with ⟨suffix, impossible⟩
                    simp [Split, stackEq] at impossible
                | cons key rest =>
                    cases rest with
                    | nil =>
                        rcases of_run_sstore sstoreRun with
                          ⟨actualKey, value, popped⟩
                        have pref := pref_of_split popped
                        rcases pref with ⟨suffix, impossible⟩
                        simp [Split, stackEq] at impossible
                    | cons value tail =>
                        intro owner storageKey
                        by_cases ownerEq : sevm.currentTarget = owner
                        · subst owner
                          have updated := sstore_getStor_set sstoreRun
                            (show [key, value] <<+ pre.stack by
                              rw [stackEq]
                              exact ⟨tail, rfl⟩)
                          rw [updated]
                          by_cases keyEq : key = storageKey
                          · subst storageKey
                            simp [Exec.Deriv.successfulSstore?, decoded,
                              stackEq, Exec.StorageWrite.replayCell,
                              Exec.StorageWrite.matches, Stor.get_set_self]
                          · simp [Exec.Deriv.successfulSstore?, decoded,
                              stackEq, Exec.StorageWrite.replayCell,
                              Exec.StorageWrite.matches, keyEq,
                              Stor.get_set_ne _ keyEq]
                        · have unchanged :=
                            sstore_preserves_getStor_ne rrun ownerEq
                          rw [unchanged]
                          simp [Exec.Deriv.successfulSstore?, decoded,
                            stackEq, Exec.StorageWrite.replayCell,
                            Exec.StorageWrite.matches, ownerEq]
              · have equal : Devm.getStor pre = Devm.getStor post :=
                  Rinst.preserves_stor store rrun
                simpa [Exec.Deriv.successfulSstore?, decoded, store] using
                  Exec.StorageReplay.of_getStor_eq equal.symm

/-- A childless successful executable spawn is persistent-storage silent. -/
private theorem Exec.doneOk_getStor_eq
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {settled : Except (EvmError × State × AdrSet × Tra) Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .done settled)
    (resumeRun : resume.run settled = .ok post) :
    Devm.getStor post = Devm.getStor pre := by
  rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
  have run : Xinst.Run sevm pre x .none (.ok post) := by
    unfold Xinst.Run XStep.Run
    rw [spawn]
    exact ⟨settled, RunFrame.of_done enter, resumeRun.symm⟩
  exact Xinst.none_getStor_eq run

/-- A committing halted driver node is a successful last instruction, hence
is persistent-storage silent. -/
private theorem Exec.halt_getStor_eq
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (committed : Execution.commits out = true) :
    Devm.getStor (Execution.committedPost out committed) =
      Devm.getStor pre := by
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
      cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
      | none =>
          unfold Evm.step at step
          rw [decoded] at step
          cases step
      | some instruction =>
          cases instruction with
          | last last =>
              rw [Evm.step_last decoded] at step
              have run : Linst.Run sevm pre last (.ok post) := by
                exact Step.halt.inj step
              exact Linst.getStor_eq run
          | next next =>
              rw [Evm.step_next decoded] at step
              exact (Ninst.step_ne_halt_ok step).elim
          | jump jumpInst =>
              rw [Evm.step_jump decoded] at step
              cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
              | error error =>
                  rw [jumpEq] at step
                  cases step
              | ok result =>
                  rw [jumpEq] at step
                  cases step

/-- The committed persistent-storage endpoint is exactly chronological replay
of the settlement-retained successful SSTORE events. -/
theorem Exec.storageReplay_committedPost
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) :
    Exec.StorageReplay pre (Execution.committedPost out committed)
      (Exec.retainedStorageWrites run) := by
  induction run with
  | halt step =>
      simpa [Exec.retainedStorageWrites, Exec.retainedNodes, committed,
        Exec.retainedNodesOfCommits, Exec.Deriv.successfulSstore?] using
        Exec.StorageReplay.of_getStor_eq
          (Exec.halt_getStor_eq step committed)
  | cont step next ih =>
      have head := Exec.storageReplay_cont_head step next
      have tail := ih committed
      convert head.append tail using 1
      simp [Exec.retainedStorageWrites, Exec.retainedNodes, committed,
        Exec.retainedNodesOfCommits, List.filterMap_cons]
      split <;> simp_all
  | doneErr step enter resume =>
      simp [Execution.commits] at committed
  | doneOk step enter resume next ih =>
      have head := Exec.StorageReplay.of_getStor_eq
        (Exec.doneOk_getStor_eq step enter resume)
      have tail := ih committed
      simpa [Exec.retainedStorageWrites, Exec.retainedNodes, committed,
        Exec.retainedNodesOfCommits, Exec.Deriv.successfulSstore?] using
        head.append tail
  | runErr step enter child resume ih =>
      simp [Execution.commits] at committed
  | runOk step enter child resume next childIH nextIH =>
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have throughChild := Xinst.storageReplay_some_of_body
        spawn (RunFrame.of_run enter) resume childIH
      have throughTail := nextIH committed
      convert throughChild.append throughTail using 1
      split
      · rename_i settles
        have rawCommits := Frame.raw_commits_of_settlementCommits settles
        simp [Exec.retainedStorageWrites, Exec.retainedNodes, committed,
          settles, rawCommits,
          Exec.retainedNodesOfCommits, List.filterMap_append,
          Exec.Deriv.successfulSstore?]
      · rename_i settles
        simp_all [Exec.retainedStorageWrites, Exec.retainedNodes,
          Exec.retainedNodesOfCommits,
          Exec.Deriv.successfulSstore?]

/-- Any committed persistent-storage change has an exact last retained
successful SSTORE witness at the same owner and raw key, recording the final
word.  Later no-op writes are included and therefore supersede earlier writes. -/
theorem Exec.exists_lastRetainedSstore_of_getStor_ne
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    {owner : Adr} {key : B256}
    (changed :
      (Devm.getStor pre owner).get key ≠
        (Devm.getStor (Execution.committedPost out committed) owner).get key) :
    ∃ write : Exec.SuccessfulSstoreOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      write.Retained ∧
      write.storageOwner = owner ∧
      write.key = key ∧
      write.value =
        (Devm.getStor (Execution.committedPost out committed) owner).get key ∧
      write.IsLastRetained := by
  exact Exec.exists_lastRetainedSstore_of_replay
    (Exec.storageReplay_committedPost run committed owner key) changed

/-- The unique same-frame continuation edge.  Entered child proofs are not
edges here: they are the chronological segment crossed by `runOk` before its
parent continuation. -/
inductive Exec.Deriv.ParentStep : Exec.Deriv → Exec.Deriv → Prop
  | cont {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .cont hstep next⟩
  | doneOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {resume : Resume}
      {settled : Except (EvmError × State × AdrSet × Tra) Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .done settled)
      (hresume : resume.run settled = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩
  | runOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .runOk hstep henter child hresume next⟩

/-- A same-frame node has only one continuation in one concrete proof. -/
theorem Exec.Deriv.ParentStep.unique
    {root nextLeft nextRight : Exec.Deriv}
    (left : Exec.Deriv.ParentStep nextLeft root)
    (right : Exec.Deriv.ParentStep nextRight root) :
    nextLeft = nextRight := by
  cases left <;> cases right <;> simp_all

/-- A same-frame parent edge is an immediate recursive derivation edge. -/
theorem Exec.Deriv.ParentStep.prec
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) : next ≺ root := by
  cases edge with
  | cont hstep next => exact .cont hstep next
  | doneOk hstep henter hresume next =>
      exact .doneOk hstep henter hresume next
  | runOk hstep henter child hresume next =>
      exact .runOkCont hstep henter child hresume next

/-- A same-frame parent edge strictly descends in the execution proof. -/
theorem Exec.Deriv.ParentStep.lt
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) : Exec.Deriv.lt next root :=
  Exec.Deriv.lt_of_prec edge.prec

/-- A finite same-frame prefix. -/
inductive Exec.Deriv.ParentPrefix : Exec.Deriv → Exec.Deriv → Prop
  | refl (root : Exec.Deriv) : ParentPrefix root root
  | step {root next tail : Exec.Deriv}
      (head : Exec.Deriv.ParentStep next root)
      (rest : Exec.Deriv.ParentPrefix next tail) :
      Exec.Deriv.ParentPrefix root tail

/-- Append one same-frame continuation edge. -/
theorem Exec.Deriv.ParentPrefix.snoc
    {root current next : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root current)
    (edge : Exec.Deriv.ParentStep next current) :
    Exec.Deriv.ParentPrefix root next := by
  induction hprefix with
  | refl => exact .step edge (.refl _)
  | step head rest ih => exact .step head (ih edge)

/-- Compose two finite same-frame prefixes. -/
private theorem Exec.Deriv.ParentPrefix.trans
    {root middle tail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root middle)
    (right : Exec.Deriv.ParentPrefix middle tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction left with
  | refl => exact right
  | step head rest ih => exact .step head (ih right)

/-- A same-frame prefix endpoint is a recursive descendant of its start. -/
private theorem Exec.Deriv.ParentPrefix.le
    {root tail : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root tail) :
    Exec.Deriv.le tail root := by
  induction hprefix with
  | refl => exact .refl _
  | step head rest ih => exact .step ih head.prec

/-- Distinct endpoints of a same-frame prefix are strictly ordered in the
descendant-first derivation order. -/
private theorem Exec.Deriv.ParentPrefix.lt_of_ne
    {root tail : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root tail)
    (distinct : root ≠ tail) : Exec.Deriv.lt tail root := by
  rcases Exec.Deriv.eq_or_lt_of_le hprefix.le with equal | strict
  · exact (distinct equal.symm).elim
  · exact strict

/-- Follow one known childless machine continuation. -/
theorem Exec.Deriv.ParentPrefix.advance_cont
    {root : Exec.Deriv} {pc nextPc : Nat} {sevm : Sevm}
    {pre nextPre : Devm} {out : Execution}
    (current : Exec pc sevm pre out)
    (hprefix : Exec.Deriv.ParentPrefix root
      ⟨pc, sevm, pre, out, current⟩)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont nextPc nextPre) :
    ∃ continuation : Exec nextPc sevm nextPre out,
      Exec.Deriv.ParentStep
          ⟨nextPc, sevm, nextPre, out, continuation⟩
          ⟨pc, sevm, pre, out, current⟩ ∧
      Exec.Deriv.ParentPrefix root
        ⟨nextPc, sevm, nextPre, out, continuation⟩ := by
  cases current with
  | halt step => cases hstep.symm.trans step
  | cont step next =>
      cases hstep.symm.trans step
      let edge : Exec.Deriv.ParentStep
          ⟨nextPc, sevm, nextPre, out, next⟩
          ⟨pc, sevm, pre, out, .cont hstep next⟩ := .cont hstep next
      exact ⟨next, edge, hprefix.snoc edge⟩
  | doneErr step enter resume => cases hstep.symm.trans step
  | doneOk step enter resume next => cases hstep.symm.trans step
  | runErr step enter child resume => cases hstep.symm.trans step
  | runOk step enter child resume next => cases hstep.symm.trans step

/-- Same-frame prefixes in a fixed execution proof are linearly ordered. -/
theorem Exec.Deriv.ParentPrefix.linear
    {root leftTail rightTail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root leftTail)
    (right : Exec.Deriv.ParentPrefix root rightTail) :
    Exec.Deriv.ParentPrefix leftTail rightTail ∨
      Exec.Deriv.ParentPrefix rightTail leftTail := by
  induction left generalizing rightTail with
  | refl => exact Or.inl right
  | step head rest ih =>
      cases right with
      | refl => exact Or.inr (.step head rest)
      | step rightHead rightRest =>
          cases head.unique rightHead
          exact ih rightRest

/-- Following a known same-frame edge characterizes every prefix from its
source as either the source itself or a prefix from the unique continuation. -/
theorem Exec.Deriv.ParentStep.parentPrefix_iff
    {root next tail : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) :
    Exec.Deriv.ParentPrefix root tail ↔
      tail = root ∨ Exec.Deriv.ParentPrefix next tail := by
  constructor
  · intro hprefix
    cases hprefix with
    | refl => exact Or.inl rfl
    | step head rest =>
        cases edge.unique head
        exact Or.inr rest
  · rintro (rfl | rest)
    · exact .refl _
    · exact .step edge rest

/-- Raw-node membership is either in the selected outer frame's same-frame
prefix or in the prefix of one of its actually entered descendant frames. -/
private theorem Exec.mem_rawNodes_iff_rawFrameDescendant_parentPrefix :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm}
      {out : Execution} (run : Exec pc sevm pre out) (node : Exec.Deriv),
      node ∈ Exec.rawNodes run ↔
        Exec.Deriv.ParentPrefix
          ⟨pc, sevm, pre, out, run⟩ node ∨
        ∃ root ∈ Exec.rawFrameDescendants run,
          Exec.Deriv.ParentPrefix root node := by
  intro pc sevm pre out run
  induction run with
  | halt hstep =>
      intro node
      constructor
      · intro h
        simp only [Exec.rawNodes, List.mem_singleton] at h
        subst node
        exact Or.inl (.refl _)
      · rintro (h | ⟨root, hroot, _⟩)
        · cases h with
          | refl => simp [Exec.rawNodes]
          | step edge _ => cases edge
        · simp [Exec.rawFrameDescendants] at hroot
  | cont hstep next ih =>
      intro node
      let edge : Exec.Deriv.ParentStep
          (⟨_, _, _, _, next⟩ : Exec.Deriv)
          (⟨_, _, _, _, Exec.cont hstep next⟩ : Exec.Deriv) :=
        .cont hstep next
      simp only [Exec.rawNodes, Exec.rawFrameDescendants, List.mem_cons, ih]
      rw [edge.parentPrefix_iff]
      aesop
  | doneErr hstep henter hresume =>
      intro node
      constructor
      · intro h
        simp only [Exec.rawNodes, List.mem_singleton] at h
        subst node
        exact Or.inl (.refl _)
      · rintro (h | ⟨root, hroot, _⟩)
        · cases h with
          | refl => simp [Exec.rawNodes]
          | step edge _ => cases edge
        · simp [Exec.rawFrameDescendants] at hroot
  | doneOk hstep henter hresume next ih =>
      intro node
      let edge : Exec.Deriv.ParentStep
          (⟨_, _, _, _, next⟩ : Exec.Deriv)
          (⟨_, _, _, _, Exec.doneOk hstep henter hresume next⟩ : Exec.Deriv) :=
        .doneOk hstep henter hresume next
      simp only [Exec.rawNodes, Exec.rawFrameDescendants, List.mem_cons, ih]
      rw [edge.parentPrefix_iff]
      aesop
  | runErr hstep henter child hresume ih =>
      intro node
      constructor
      · intro h
        simp only [Exec.rawNodes, List.mem_cons] at h
        rcases h with rfl | hchild
        · exact Or.inl (.refl _)
        · right
          rcases (ih node).mp hchild with
            hprefix | ⟨root, hroot, hprefix⟩
          · exact ⟨⟨_, _, _, _, child⟩,
              by simp [Exec.rawFrameDescendants], hprefix⟩
          · exact ⟨root,
              by simp [Exec.rawFrameDescendants, hroot], hprefix⟩
      · rintro (hprefix | ⟨root, hroot, hprefix⟩)
        · cases hprefix with
          | refl => simp [Exec.rawNodes]
          | step edge _ => cases edge
        · simp only [Exec.rawFrameDescendants, List.mem_cons] at hroot
          rcases hroot with rfl | hroot
          · simp only [Exec.rawNodes, List.mem_cons]
            exact Or.inr ((ih node).mpr (Or.inl hprefix))
          · simp only [Exec.rawNodes, List.mem_cons]
            exact Or.inr ((ih node).mpr
              (Or.inr ⟨root, hroot, hprefix⟩))
  | runOk hstep henter child hresume next childIh nextIh =>
      intro node
      let edge : Exec.Deriv.ParentStep
          (⟨_, _, _, _, next⟩ : Exec.Deriv)
          (⟨_, _, _, _, Exec.runOk hstep henter child hresume next⟩ :
            Exec.Deriv) :=
        .runOk hstep henter child hresume next
      constructor
      · intro h
        simp only [Exec.rawNodes, List.mem_cons, List.mem_append] at h
        rcases h with rfl | hrest
        · exact Or.inl (.refl _)
        · rcases hrest with hchild | hnext
          · right
            rcases (childIh node).mp hchild with
              hprefix | ⟨root, hroot, hprefix⟩
            · exact ⟨⟨_, _, _, _, child⟩,
                by simp [Exec.rawFrameDescendants], hprefix⟩
            · exact ⟨root,
                by simp [Exec.rawFrameDescendants, hroot], hprefix⟩
          · rcases (nextIh node).mp hnext with
              hprefix | ⟨root, hroot, hprefix⟩
            · exact Or.inl (.step edge hprefix)
            · exact Or.inr ⟨root,
                by simp [Exec.rawFrameDescendants, hroot], hprefix⟩
      · rintro (hprefix | ⟨root, hroot, hprefix⟩)
        · rw [edge.parentPrefix_iff] at hprefix
          rcases hprefix with rfl | hnext
          · simp [Exec.rawNodes]
          · simp only [Exec.rawNodes, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr
              ((nextIh node).mpr (Or.inl hnext)))
        · simp only [Exec.rawFrameDescendants, List.mem_cons,
            List.mem_append] at hroot
          simp only [Exec.rawNodes, List.mem_cons, List.mem_append]
          rcases hroot with rfl | hrest
          · exact Or.inr (Or.inl
              ((childIh node).mpr (Or.inl hprefix)))
          · rcases hrest with hchild | hnext
            · exact Or.inr (Or.inl
                ((childIh node).mpr
                  (Or.inr ⟨root, hchild, hprefix⟩)))
            · exact Or.inr (Or.inr
                ((nextIh node).mpr
                  (Or.inr ⟨root, hnext, hprefix⟩)))

/-- Exact all-outcome frame ownership of raw chronology.  No commitment,
settlement, uniqueness, or `Nodup` claim is involved. -/
theorem Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (node : Exec.Deriv) :
    node ∈ Exec.rawNodes run ↔
      ∃ root ∈ Exec.rawFrameRoots run,
        Exec.Deriv.ParentPrefix root node := by
  rw [Exec.mem_rawNodes_iff_rawFrameDescendant_parentPrefix run node]
  simp only [Exec.rawFrameRoots, List.mem_cons]
  aesop

/-- Same-frame strengthening of `Exec.rawFrameDescendants_eq_nil_of_no_xinstAt`:
only the outer root's own continuation chain has to be free of executable
instructions, because the first frame entered anywhere would be spawned on
that chain.  A source-level "this program has no such instruction" fact is
normally available only for same-frame nodes, so this is the form such a fact
can discharge. -/
theorem Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (childless : ∀ node : Exec.Deriv,
      Exec.Deriv.ParentPrefix (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) node →
        ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    Exec.rawFrameDescendants run = [] := by
  induction run with
  | halt => simp [Exec.rawFrameDescendants]
  | cont hstep next ih =>
      simp only [Exec.rawFrameDescendants]
      exact ih fun node hprefix =>
        childless node (.step (.cont hstep next) hprefix)
  | doneErr => simp [Exec.rawFrameDescendants]
  | doneOk hstep henter hresume next ih =>
      simp only [Exec.rawFrameDescendants]
      exact ih fun node hprefix =>
        childless node (.step (.doneOk hstep henter hresume next) hprefix)
  | runErr hstep henter child hresume childIh =>
      rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
      exact absurd decoded (childless _ (.refl _) x)
  | runOk hstep henter child hresume next childIh nextIh =>
      rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
      exact absurd decoded (childless _ (.refl _) x)

/-- With no entered child frame the raw chronology is exactly the outer root's
own same-frame continuation chain.  This converts frame-entry freedom into the
`ParentPrefix` premise that same-frame attribution theorems take. -/
theorem Exec.Deriv.parentPrefix_of_mem_rawNodes_of_rawFrameDescendants_eq_nil
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {node : Exec.Deriv}
    (childless : Exec.rawFrameDescendants run = [])
    (reached : node ∈ Exec.rawNodes run) :
    Exec.Deriv.ParentPrefix (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) node := by
  rcases (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run node).mp
      reached with ⟨root, member, hprefix⟩
  rw [Exec.rawFrameRoots, childless, List.mem_singleton] at member
  exact member ▸ hprefix

/-- Under a committing root, retained-node membership is exactly membership in
the root frame's same-frame prefix or in one of its landed descendant frames. -/
private theorem Exec.mem_retainedNodesOfCommits_iff_parentPrefix
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (node : Exec.Deriv) :
    node ∈ Exec.retainedNodesOfCommits run committed ↔
      Exec.Deriv.ParentPrefix
          (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) node ∨
        ∃ frame ∈ Exec.descendantFrames run,
          Exec.Deriv.ParentPrefix frame.rootDeriv node := by
  induction run with
  | halt hstep =>
      constructor
      · intro member
        simp only [Exec.retainedNodesOfCommits, List.mem_singleton] at member
        subst node
        exact Or.inl (.refl _)
      · rintro (hprefix | ⟨frame, member, _⟩)
        · cases hprefix with
          | refl => simp [Exec.retainedNodesOfCommits]
          | step edge _ => cases edge
        · simp [Exec.descendantFrames] at member
  | cont hstep next ih =>
      let edge : Exec.Deriv.ParentStep
          (⟨_, _, _, _, next⟩ : Exec.Deriv)
          (⟨_, _, _, _, Exec.cont hstep next⟩ : Exec.Deriv) :=
        .cont hstep next
      simp only [Exec.retainedNodesOfCommits, Exec.descendantFrames,
        List.mem_cons, ih committed]
      rw [edge.parentPrefix_iff]
      aesop
  | doneErr hstep henter hresume => simp [Execution.commits] at committed
  | doneOk hstep henter hresume next ih =>
      let edge : Exec.Deriv.ParentStep
          (⟨_, _, _, _, next⟩ : Exec.Deriv)
          (⟨_, _, _, _, Exec.doneOk hstep henter hresume next⟩ : Exec.Deriv) :=
        .doneOk hstep henter hresume next
      simp only [Exec.retainedNodesOfCommits, Exec.descendantFrames,
        List.mem_cons, ih committed]
      rw [edge.parentPrefix_iff]
      aesop
  | runErr hstep henter child hresume =>
      simp [Execution.commits] at committed
  | runOk hstep henter child hresume next childIh nextIh =>
      let edge : Exec.Deriv.ParentStep
          (⟨_, _, _, _, next⟩ : Exec.Deriv)
          (⟨_, _, _, _, Exec.runOk hstep henter child hresume next⟩ :
            Exec.Deriv) :=
        .runOk hstep henter child hresume next
      simp only [Exec.retainedNodesOfCommits, Exec.descendantFrames,
        List.mem_cons, List.mem_append]
      split
      next childSettles =>
        have childCommits :=
          Frame.raw_commits_of_settlementCommits childSettles
        simp only [childIh childCommits, nextIh committed, List.mem_cons]
        rw [edge.parentPrefix_iff]
        simp only [Exec.Frame.rootDeriv, Exec.Frame.ofRun]
        aesop
      next childDoesNotSettle =>
        simp only [List.not_mem_nil, false_or, nextIh committed]
        rw [edge.parentPrefix_iff]
        aesop

/-- A node survives settlement exactly when it is owned by the same-frame
prefix of one of `committedFrames`.  This is the membership counterpart of
`committedFrameRoots_sublist_retainedNodes`; together they link the retained
instruction chronology to the existing full-settlement frame substrate. -/
theorem Exec.mem_retainedNodes_iff_committedFrame_parentPrefix
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (node : Exec.Deriv) :
    node ∈ Exec.retainedNodes run ↔
      ∃ frame ∈ Exec.committedFrames run,
        Exec.Deriv.ParentPrefix frame.rootDeriv node := by
  unfold Exec.retainedNodes Exec.committedFrames
  split
  next committed =>
    rw [Exec.mem_retainedNodesOfCommits_iff_parentPrefix run committed node]
    simp only [List.mem_cons, Exec.Frame.rootDeriv, Exec.Frame.ofRun]
    aesop
  next notCommitted => simp

/-- One same-frame edge splits the global chronology.  A successful entered
child belongs to the nonempty crossed prefix before the parent resumes. -/
theorem Exec.Deriv.ParentStep.rawNodes_decomposition
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) :
    ∃ crossed : List Exec.Deriv,
      crossed ≠ [] ∧
      Exec.rawNodes root.exc = crossed ++ Exec.rawNodes next.exc := by
  cases edge with
  | cont hstep next =>
      refine ⟨[⟨_, _, _, _, .cont hstep next⟩], by simp, ?_⟩
      simp [Exec.rawNodes]
  | doneOk hstep henter hresume next =>
      refine ⟨[⟨_, _, _, _, .doneOk hstep henter hresume next⟩], by simp, ?_⟩
      simp [Exec.rawNodes]
  | runOk hstep henter child hresume next =>
      refine ⟨⟨_, _, _, _, .runOk hstep henter child hresume next⟩ ::
        Exec.rawNodes child, by simp, ?_⟩
      simp [Exec.rawNodes]

/-- Every same-frame prefix gives an exact split of the enclosing global
chronology at its endpoint. -/
theorem Exec.Deriv.ParentPrefix.rawNodes_decomposition
    {root tail : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root tail) :
    ∃ before : List Exec.Deriv,
      Exec.rawNodes root.exc = before ++ Exec.rawNodes tail.exc := by
  induction hprefix with
  | refl => exact ⟨[], rfl⟩
  | step head rest ih =>
      rcases head.rawNodes_decomposition with ⟨crossed, _, hhead⟩
      rcases ih with ⟨before, hrest⟩
      exact ⟨crossed ++ before, by rw [hhead, hrest, List.append_assoc]⟩

theorem Ninst.At.false_of_jinstAt
    {code : ByteArray} {pc : Nat} {n : Ninst} {j : Jinst}
    (nextAt : Ninst.At code pc n) (jumpAt : Jinst.At code pc j) : False := by
  unfold Ninst.At at nextAt
  unfold Jinst.At at jumpAt
  rw [nextAt] at jumpAt
  cases jumpAt

theorem Ninst.At.false_of_linstAt
    {code : ByteArray} {pc : Nat} {n : Ninst} {instruction : Linst}
    (nextAt : Ninst.At code pc n)
    (lastAt : Linst.At code pc instruction) : False := by
  unfold Ninst.At at nextAt
  unfold Linst.At at lastAt
  rw [nextAt] at lastAt
  cases lastAt

/-- A terminal instruction cannot have a same-frame continuation edge. -/
theorem Exec.Deriv.ParentStep.false_of_linstAt
    {root next : Exec.Deriv} {instruction : Linst}
    (edge : Exec.Deriv.ParentStep next root)
    (lastAt : Linst.At root.sevm.code root.pc instruction) : False := by
  cases edge with
  | cont hstep next => cases (Evm.step_last lastAt).symm.trans hstep
  | doneOk hstep henter hresume next =>
      cases (Evm.step_last lastAt).symm.trans hstep
  | runOk hstep henter child hresume next =>
      cases (Evm.step_last lastAt).symm.trans hstep

/-- A same-frame compiler prefix containing no SSTORE instruction boundary. -/
inductive Exec.Deriv.ParentNonSstorePrefix :
    Exec.Deriv → Exec.Deriv → Prop
  | refl (root) : ParentNonSstorePrefix root root
  | step {root next tail}
      (edge : Exec.Deriv.ParentStep next root)
      (notStore : ¬ Ninst.At root.sevm.code root.pc (.reg .sstore))
      (rest : ParentNonSstorePrefix next tail) :
      ParentNonSstorePrefix root tail

/-- Forget the compiler-only non-SSTORE annotations while retaining the
actual same-frame execution prefix. -/
private theorem Exec.Deriv.ParentNonSstorePrefix.toParentPrefix
    {root tail : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentNonSstorePrefix root tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction hprefix with
  | refl => exact .refl _
  | step edge notStore rest ih => exact .step edge ih

/-- Remove compiler-only non-SSTORE nodes from the front of a reached SSTORE
prefix. -/
theorem Exec.Deriv.ParentNonSstorePrefix.trim
    {start tail occurrence : Exec.Deriv}
    (compilerPrefix : Exec.Deriv.ParentNonSstorePrefix start tail)
    (reached : Exec.Deriv.ParentPrefix start occurrence)
    (storeAt : Ninst.At occurrence.sevm.code occurrence.pc (.reg .sstore)) :
    Exec.Deriv.ParentPrefix tail occurrence := by
  induction compilerPrefix generalizing occurrence with
  | refl => exact reached
  | step edge notStore rest ih =>
      cases reached with
      | refl => exact (notStore storeAt).elim
      | step occurrenceEdge suffix =>
          cases edge.unique occurrenceEdge
          exact ih suffix storeAt

/-- Compiler-prefix endpoints are recursive descendants of their starts. -/
theorem Exec.Deriv.ParentNonSstorePrefix.le
    {start tail : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentNonSstorePrefix start tail) :
    Exec.Deriv.le tail start := by
  induction hprefix with
  | refl => exact .refl _
  | step edge notStore rest ih => exact .step ih edge.prec

/-- A nonempty compiler prefix strictly descends in the execution proof. -/
theorem Exec.Deriv.ParentNonSstorePrefix.lt_of_step
    {start next tail : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next start)
    (_notStore : ¬ Ninst.At start.sevm.code start.pc (.reg .sstore))
    (rest : Exec.Deriv.ParentNonSstorePrefix next tail) :
    Exec.Deriv.lt tail start :=
  ⟨next, rest.le, edge.prec⟩

/-- A source instruction that cannot be compiler PUSH glue. -/
def NinstNonPush : Ninst → Prop
  | .push _ _ => False
  | _ => True

/-- Cross an actually executed compiler PUSH only when the nominated non-PUSH
source target lies later in the same-frame prefix. -/
private theorem Exec.Deriv.ParentPrefix.advance_pushToward
    {start target : Exec.Deriv} {xs : Bytes} {targetInstruction : Ninst}
    (reached : Exec.Deriv.ParentPrefix start target)
    (pushAt : PushAt start.sevm.code start.pc xs)
    (hne : xs ≠ [])
    (targetNonPush : NinstNonPush targetInstruction)
    (storeAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ (inter : Devm)
      (next : Exec (start.pc + xs.length + 1) start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ target ∧
      Devm.PushBurn [xs.toB256] start.devm inter := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  rcases pushAt with ⟨le, pushAt⟩
  cases reached with
  | refl =>
      have impossible := Ninst.at_unique storeAt pushAt
      subst targetInstruction
      exact targetNonPush.elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          have sourceStep := hstatic.symm.trans hstep
          rw [Ninst.step_push, if_neg hne] at sourceStep
          obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont sourceStep
          cases hpc
          exact ⟨_, next, .cont hstep next, rest,
            Devm.pushBurn_of_run hrun⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim

/-- Cross an actually executed compiler jump only when the nominated source
target lies later in the same-frame prefix. -/
private theorem Exec.Deriv.ParentPrefix.advance_jumpToward
    {start target : Exec.Deriv} {instruction : Jinst}
    {targetInstruction : Ninst}
    (reached : Exec.Deriv.ParentPrefix start target)
    (jumpAt : Jinst.At start.sevm.code start.pc instruction)
    (storeAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ (nextPc : Nat) (inter : Devm)
      (next : Exec nextPc start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ target ∧
      Jinst.Run ⟨start.pc, start.sevm, start.devm⟩ instruction
        (.ok ⟨nextPc, inter⟩) := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  dsimp at reached storeAt jumpAt
  cases reached with
  | refl => exact (storeAt.false_of_jinstAt jumpAt).elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact ⟨_, _, next, .cont hstep next, rest,
            Step.ofJump_cont (hstatic.symm.trans hstep)⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim

/-! ## Executable compiler source sites -/

/-- One structural descent in a source `Func`.  Compiler-only control-flow
bytes are deliberately absent. -/
inductive Prog.SourceStep where
  | rest
  | branchLeft
  | branchRight
deriving DecidableEq, Repr

/-- Stable structural identity of a source instruction. -/
structure Prog.SourcePath where
  functionIndex : Nat
  steps : List Prog.SourceStep
deriving DecidableEq, Repr

/-- An executable compiler-produced source instruction site. -/
structure Prog.SourceSite where
  path : Prog.SourcePath
  pc : Nat
  instruction : Ninst

/-- Enumerate exactly the `.next` nodes of a source function at their compiled
program counters.  `branch` and `call` contribute only compiler glue, so they
do not themselves produce source sites. -/
def Func.sourceSites (functionIndex : Nat) (steps : List Prog.SourceStep)
    (pc : Nat) : Func → List Prog.SourceSite
  | .last _ => []
  | .next instruction tail =>
      { path := ⟨functionIndex, steps⟩, pc, instruction } ::
        Func.sourceSites functionIndex (steps ++ [.rest])
          (pc + instruction.size) tail
  | .branch left right =>
      Func.sourceSites functionIndex (steps ++ [.branchLeft]) (pc + 4) left ++
        Func.sourceSites functionIndex (steps ++ [.branchRight])
          (pc + compsize left + 5) right
  | .call _ => []

/-- Executable source map for every function body in compiler-table order. -/
def Prog.sourceSites (program : Prog) : List Prog.SourceSite :=
  (List.range (program.main :: program.aux).length).flatMap fun index =>
    match (table 0 (program.main :: program.aux))[index]? with
    | some (pc, body) => Func.sourceSites index [] (pc + 1) body
    | none => []

/-- Look up a source site by compiled program counter. -/
def Prog.sourceSiteAt (program : Prog) (pc : Nat) : Option Prog.SourceSite :=
  program.sourceSites.find? fun site => site.pc == pc

/-- Every enumerated function site decodes to its recorded instruction in the
compiler output. -/
theorem Func.sourceSites_sound
    {code : ByteArray} {layout : List (Nat × Func)}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {pc : Nat} {body : Func} {site : Prog.SourceSite}
    (sub : subcode code.toList pc (Func.compile layout pc body))
    (boundary : noPushBefore code pc 32 = true)
    (member : site ∈ Func.sourceSites functionIndex steps pc body) :
    Ninst.At code site.pc site.instruction := by
  induction body generalizing pc steps with
  | last outcome =>
      simp [Func.sourceSites] at member
  | next instruction tail ih =>
      simp only [Func.sourceSites, List.mem_cons] at member
      rcases member with rfl | member
      · rcases of_subcode sub with ⟨compiled, hcompile, hslice⟩
        rcases of_bind_eq_some hcompile with ⟨tailBytes, htail, hwhole⟩
        rw [← of_pure_eq_some hwhole] at hslice
        exact Ninst.at_of_slice (List.slice_prefix hslice)
      · rcases Func.noPushBefore_next sub boundary with
          ⟨nextBoundary, nextSub⟩
        exact ih nextSub nextBoundary member
  | branch left right left_ih right_ih =>
      simp only [Func.sourceSites, List.mem_append] at member
      rcases subcode_compile_branch_jumpable sub boundary with
        ⟨loc, hloc, _, _, _, leftSub, leftBoundary, _, _, rightSub,
          rightBoundary⟩
      rcases member with leftMember | rightMember
      · exact left_ih leftSub leftBoundary leftMember
      · have hpc : loc + 1 = pc + compsize left + 5 := by omega
        rw [hpc] at rightSub rightBoundary
        exact right_ih rightSub rightBoundary rightMember
  | call index =>
      simp [Func.sourceSites] at member

/-- The program-level source map is sound against the exact compiler output. -/
theorem Prog.sourceSites_sound
    {program : Prog} {code : ByteArray} {site : Prog.SourceSite}
    (compiled : some code.toList = program.compile)
    (member : site ∈ program.sourceSites) :
    Ninst.At code site.pc site.instruction := by
  simp only [Prog.sourceSites, List.mem_flatMap] at member
  rcases member with ⟨index, index_mem, member⟩
  split at member
  next body hentry =>
    have sub := (subcode_of_get?_eq_some compiled hentry).2
    have boundary := (Prog.jumpable_of_get?_table compiled hentry).2
    exact Func.sourceSites_sound sub boundary member
  next hnone =>
    simp at member

/-- A successful executable lookup has the requested PC and decodes exactly
as recorded. -/
theorem Prog.sourceSiteAt_sound
    {program : Prog} {code : ByteArray} {pc : Nat} {site : Prog.SourceSite}
    (compiled : some code.toList = program.compile)
    (found : program.sourceSiteAt pc = some site) :
    site.pc = pc ∧ Ninst.At code site.pc site.instruction := by
  constructor
  · have h := List.find?_some found
    simpa [BEq.beq] using h
  · exact program.sourceSites_sound compiled
      (List.mem_of_find?_eq_some found)

/-! ## Exact invocation identity -/

/-- Exact contract-neutral identity of an arbitrary-outcome code-frame root.
It pins the entry PC, storage target, code address, and compiled bytes, but no
commitment, settlement, installation, or call-opcode fact. -/
def Exec.Deriv.exactInvocation
    (program : Prog) (storageTarget codeAddress : Adr)
    (root : Exec.Deriv) : Prop :=
  root.pc = 0 ∧
    root.sevm.currentTarget = storageTarget ∧
    root.sevm.codeAddress = some codeAddress ∧
    some root.sevm.code.toList = program.compile

instance (program : Prog) (storageTarget codeAddress : Adr)
    (root : Exec.Deriv) :
    Decidable (root.exactInvocation program storageTarget codeAddress) := by
  unfold Exec.Deriv.exactInvocation
  infer_instance

/-- Exact contract-neutral identity of one retained compiled invocation.
`currentTarget` is the storage owner, `codeAddress` names the executing code
account, and the final conjunct pins the exact execution bytes.  Installation
in the entry state and call-opcode provenance are intentionally separate. -/
def Exec.Frame.exactInvocation
    (program : Prog) (storageTarget codeAddress : Adr)
    (frame : Exec.Frame) : Prop :=
  frame.pc = 0 ∧
    frame.sevm.currentTarget = storageTarget ∧
    frame.sevm.codeAddress = some codeAddress ∧
    some frame.sevm.code.toList = program.compile

instance (program : Prog) (storageTarget codeAddress : Adr)
    (frame : Exec.Frame) :
    Decidable (frame.exactInvocation program storageTarget codeAddress) := by
  unfold Exec.Frame.exactInvocation
  infer_instance

/-- The landed committed-frame identity is exactly the raw identity of its
root derivation; the commit proof adds no identity conjunct. -/
theorem Exec.Frame.exactInvocation_iff_rootDeriv
    {frame : Exec.Frame} {program : Prog} {storageTarget codeAddress : Adr} :
    frame.exactInvocation program storageTarget codeAddress ↔
      frame.rootDeriv.exactInvocation program storageTarget codeAddress := by
  rfl

@[simp] theorem table_length (start : Nat) (functions : List Func) :
    (table start functions).length = functions.length := by
  induction functions generalizing start with
  | nil => rfl
  | cons head tail ih => simp [table, ih]

/-- Canonical arbitrary-outcome cursor connecting one actually reached node of
a selected raw frame root to one compiler source body. -/
structure Exec.Deriv.SourceCursor
    (root : Exec.Deriv) (program : Prog)
    (path : Prog.SourcePath) (source : Func) where
  pc : Nat
  pre : Devm
  current : Exec pc root.sevm pre root.exn
  parentPrefix : Exec.Deriv.ParentPrefix root
    ⟨pc, root.sevm, pre, root.exn, current⟩
  codeSlice : subcode root.sevm.code.toList pc
    (Func.compile (table 0 (program.main :: program.aux)) pc source)
  codeBoundary : noPushBefore root.sevm.code pc 32 = true
  sourceIncluded : ∀ {site},
    site ∈ Func.sourceSites path.functionIndex path.steps pc source →
      site ∈ program.sourceSites

/-- The reached derivation selected by an arbitrary-outcome source cursor. -/
def Exec.Deriv.SourceCursor.node
    {root : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Deriv.SourceCursor root program path source) : Exec.Deriv :=
  ⟨cursor.pc, root.sevm, cursor.pre, root.exn, cursor.current⟩

/-- Enter the main source body only when the nominated source target proves
that execution crossed the compiler's leading `JUMPDEST`.  An exact compiled
root that fails at that glue instruction therefore yields no unconditional
body cursor. -/
theorem Exec.Deriv.SourceCursor.mainToward
    {root target : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr} {targetInstruction : Ninst}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (reached : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ cursor : Exec.Deriv.SourceCursor root program ⟨0, []⟩ program.main,
      Exec.Deriv.ParentNonSstorePrefix root cursor.node ∧
      Exec.Deriv.ParentPrefix cursor.node target := by
  rcases root with ⟨pc, sevm, pre, out, run⟩
  rcases invocation with ⟨hpc, htarget, haddress, hcode⟩
  dsimp at hpc htarget haddress hcode reached storeAt
  subst pc
  have hget :
      (table 0 (program.main :: program.aux))[0]? =
        some (0, program.main) := rfl
  rcases subcode_of_get?_eq_some hcode hget with
    ⟨jumpdestAt, sourceSlice⟩
  have sourceBoundary : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table hcode hget).2
  cases reached with
  | refl =>
      exact (storeAt.false_of_jinstAt jumpdestAt).elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          have jrun :
              Jinst.Run ⟨0, sevm, pre⟩ .jumpdest (.ok ⟨_, _⟩) :=
            Step.ofJump_cont (hstatic.symm.trans hstep)
          rcases of_jumpdest_run jrun with ⟨eqPc, burn⟩
          cases eqPc
          let nextNode : Exec.Deriv := ⟨1, sevm, _, out, next⟩
          let parentEdge : Exec.Deriv.ParentStep nextNode
              ⟨0, sevm, pre, out, .cont hstep next⟩ :=
            .cont hstep next
          have parentPrefix : Exec.Deriv.ParentPrefix
              ⟨0, sevm, pre, out, .cont hstep next⟩ nextNode :=
            .step parentEdge (.refl _)
          let cursor : Exec.Deriv.SourceCursor
              ⟨0, sevm, pre, out, .cont hstep next⟩ program
              ⟨0, []⟩ program.main :=
            ⟨1, _, next, parentPrefix, sourceSlice, sourceBoundary, by
              intro site member
              simp only [Prog.sourceSites, List.mem_flatMap]
              refine ⟨0, by simp, ?_⟩
              simpa only [hget] using member⟩
          have notStore : ¬ Ninst.At sevm.code 0 (.reg .sstore) := by
            intro storeHere
            exact storeHere.false_of_jinstAt jumpdestAt
          exact ⟨cursor, .step parentEdge notStore (.refl _), rest⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim

/-- Advance a source `.next` only when the target prefix supplies the actual
same-frame continuation edge.  This permits an erroring current source
instruction to be attributed without inventing a tail cursor. -/
theorem Exec.Deriv.SourceCursor.nextOfParentStep
    {root nextNode : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail))
    (edge : Exec.Deriv.ParentStep nextNode cursor.node) :
    ∃ nextCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail,
      nextCursor.node = nextNode := by
  rcases cursor with
    ⟨cursorPc, cursorPre, current, parentPrefix, codeSlice, codeBoundary,
      sourceIncluded⟩
  change Exec.Deriv.ParentStep nextNode
    ⟨cursorPc, root.sevm, cursorPre, root.exn, current⟩ at edge
  have sourceAt : Ninst.At root.sevm.code cursorPc instruction :=
    Func.sourceSites_sound codeSlice codeBoundary
      (functionIndex := path.functionIndex) (steps := path.steps)
      (site := { path := path, pc := cursorPc, instruction := instruction })
      (by rcases path with ⟨functionIndex, steps⟩
          simp [Func.sourceSites])
  rcases Func.noPushBefore_next codeSlice codeBoundary with
    ⟨tailBoundary, tailSlice⟩
  cases edge with
  | cont hstep next =>
      have sourceStep := (Evm.step_next sourceAt).symm.trans hstep
      cases Ninst.step_cont_pc sourceStep
      let nextEdge : Exec.Deriv.ParentStep
          ⟨cursorPc + instruction.size, root.sevm, _, root.exn, next⟩
          ⟨cursorPc, root.sevm, cursorPre, root.exn, .cont hstep next⟩ :=
        .cont hstep next
      have nextPrefix := parentPrefix.snoc nextEdge
      refine ⟨⟨_, _, next, nextPrefix, tailSlice, tailBoundary, ?_⟩, rfl⟩
      intro site member
      apply sourceIncluded
      simp [Func.sourceSites, member]
  | doneOk hstep henter hresume next =>
      have sourceStep := (Evm.step_next sourceAt).symm.trans hstep
      cases Ninst.step_spawn_pc sourceStep
      let nextEdge : Exec.Deriv.ParentStep
          ⟨cursorPc + instruction.size, root.sevm, _, root.exn, next⟩
          ⟨cursorPc, root.sevm, cursorPre, root.exn,
            .doneOk hstep henter hresume next⟩ :=
        .doneOk hstep henter hresume next
      have nextPrefix := parentPrefix.snoc nextEdge
      refine ⟨⟨_, _, next, nextPrefix, tailSlice, tailBoundary, ?_⟩, rfl⟩
      intro site member
      apply sourceIncluded
      simp [Func.sourceSites, member]
  | runOk hstep henter child hresume next =>
      have sourceStep := (Evm.step_next sourceAt).symm.trans hstep
      cases Ninst.step_spawn_pc sourceStep
      let nextEdge : Exec.Deriv.ParentStep
          ⟨cursorPc + instruction.size, root.sevm, _, root.exn, next⟩
          ⟨cursorPc, root.sevm, cursorPre, root.exn,
            .runOk hstep henter child hresume next⟩ :=
        .runOk hstep henter child hresume next
      have nextPrefix := parentPrefix.snoc nextEdge
      refine ⟨⟨_, _, next, nextPrefix, tailSlice, tailBoundary, ?_⟩, rfl⟩
      intro site member
      apply sourceIncluded
      simp [Func.sourceSites, member]

/-- Select the source branch arm that contains the nominated reached source
instruction.
Every crossed compiler instruction is justified by the target prefix, so this
works independently of the selected frame's final outcome. -/
theorem Exec.Deriv.SourceCursor.branchToward
    {root target : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {left right : Func} {targetInstruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.branch left right))
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (targetNonPush : NinstNonPush targetInstruction)
    (storeAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    (∃ arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.ParentNonSstorePrefix cursor.node arm.node ∧
      Exec.Deriv.ParentPrefix arm.node target ∧
      Exec.Deriv.lt arm.node cursor.node) ∨
    (∃ arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
      Exec.Deriv.ParentNonSstorePrefix cursor.node arm.node ∧
      Exec.Deriv.ParentPrefix arm.node target ∧
      Exec.Deriv.lt arm.node cursor.node) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, hlocEq, hloc, pushAt, jumpiAt, leftSlice, leftBoundary,
      jumpdestAt, jumpable, rightSlice, rightBoundary⟩
  rcases reached.advance_pushToward ⟨_, pushAt⟩ (by simp)
      targetNonPush storeAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ hloc] at pushBurn
  rcases afterPushReached.advance_jumpToward jumpiAt storeAt with
    ⟨nextPc, armPre, armExec, jumpEdge, armReached, jumpRun⟩
  rcases of_jumpi_run jumpRun with
    ⟨x, nextPcEq, popBurn⟩ | ⟨x, flag, nextPcEq, popBurn,
      actualJumpable, nonzero⟩
  · cases nextPcEq
    let armCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left :=
      ⟨_, _, armExec, cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge,
        leftSlice, leftBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          exact Or.inl member⟩
    have pushNotStore : ¬ Ninst.At root.sevm.code cursor.pc
        (.reg .sstore) := by
      intro storeHere
      have impossible := Ninst.at_unique storeHere pushAt
      cases impossible
    have jumpNotStore : ¬ Ninst.At root.sevm.code (cursor.pc + 3)
        (.reg .sstore) := by
      intro storeHere
      exact storeHere.false_of_jinstAt jumpiAt
    let compilerPrefix : Exec.Deriv.ParentNonSstorePrefix
        cursor.node armCursor.node :=
      .step pushEdge pushNotStore
        (.step jumpEdge jumpNotStore (.refl _))
    refine Or.inl ⟨armCursor, compilerPrefix, armReached, ?_⟩
    exact Exec.Deriv.ParentNonSstorePrefix.lt_of_step
      pushEdge pushNotStore (.step jumpEdge jumpNotStore (.refl _))
  · have hloc256 : loc < 2 ^ 256 := by
      apply Nat.lt_trans hloc
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have hxeq : loc = x.toNat := by
      rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
        ⟨hx, stack, pushBurn', popBurn'⟩
      have hlocToNat : loc.toB256.toNat = loc :=
        B256.toNat_toB256_of_lt hloc256
      rw [← congrArg B256.toNat hx, hlocToNat]
    have nextPcLoc : nextPc = loc := nextPcEq.trans hxeq.symm
    cases nextPcLoc
    rcases armReached.advance_jumpToward jumpdestAt storeAt with
      ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
        jumpdestRun⟩
    rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
    subst bodyPc
    let armCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right :=
      ⟨_, _, bodyExec,
        cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
          |>.snoc jumpdestEdge,
        rightSlice, rightBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          apply Or.inr
          have hrightPc : loc + 1 = cursor.pc + compsize left + 5 := by
            omega
          rw [← hrightPc]
          exact member⟩
    have pushNotStore : ¬ Ninst.At root.sevm.code cursor.pc
        (.reg .sstore) := by
      intro storeHere
      have impossible := Ninst.at_unique storeHere pushAt
      cases impossible
    have jumpNotStore : ¬ Ninst.At root.sevm.code (cursor.pc + 3)
        (.reg .sstore) := by
      intro storeHere
      exact storeHere.false_of_jinstAt jumpiAt
    have jumpdestNotStore : ¬ Ninst.At root.sevm.code loc
        (.reg .sstore) := by
      intro storeHere
      exact storeHere.false_of_jinstAt jumpdestAt
    let compilerPrefix : Exec.Deriv.ParentNonSstorePrefix
        cursor.node armCursor.node :=
      .step pushEdge pushNotStore
        (.step jumpEdge jumpNotStore
          (.step jumpdestEdge jumpdestNotStore (.refl _)))
    refine Or.inr ⟨armCursor, compilerPrefix, bodyReached, ?_⟩
    exact Exec.Deriv.ParentNonSstorePrefix.lt_of_step
      pushEdge pushNotStore
      (.step jumpEdge jumpNotStore
        (.step jumpdestEdge jumpdestNotStore (.refl _)))

/-- Follow the internal source call whose body contains the nominated reached
source instruction. The target prefix supplies the successful
PUSH/JUMP/JUMPDEST edges; the selected frame itself may finish with any
outcome. -/
theorem Exec.Deriv.SourceCursor.callToward
    {root target : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {index : Nat} {targetInstruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path (.call index))
    (compiled : some root.sevm.code.toList = program.compile)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (targetNonPush : NinstNonPush targetInstruction)
    (storeAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ body, (program.main :: program.aux)[index]? = some body ∧
      ∃ bodyCursor : Exec.Deriv.SourceCursor root program ⟨index, []⟩ body,
        Exec.Deriv.ParentNonSstorePrefix cursor.node bodyCursor.node ∧
        Exec.Deriv.ParentPrefix bodyCursor.node target ∧
        Exec.Deriv.lt bodyCursor.node cursor.node := by
  rcases subcode_compile_call cursor.codeSlice with
    ⟨loc, body, hgetTable, hloc, pushAt, jumpAt⟩
  rcases pushAt with ⟨pushLe, pushAt⟩
  have hgetBody : (program.main :: program.aux)[index]? = some body := by
    have h := @Prog.get?_table 0 index (program.main :: program.aux)
    rw [hgetTable] at h
    simpa using h.symm
  rcases reached.advance_pushToward ⟨pushLe, pushAt⟩ (by simp)
      targetNonPush storeAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ hloc] at pushBurn
  rcases afterPushReached.advance_jumpToward jumpAt storeAt with
    ⟨nextPc, beforeJumpdestPre, beforeJumpdest, jumpEdge,
      beforeJumpdestReached, jumpRun⟩
  rcases of_jump_run jumpRun with
    ⟨x, nextPcEq, popBurn, actualJumpable⟩
  have hloc256 : loc < 2 ^ 256 := by
    apply Nat.lt_trans hloc
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have hxeq : loc = x.toNat := by
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have hlocToNat : loc.toB256.toNat = loc :=
      B256.toNat_toB256_of_lt hloc256
    rw [← congrArg B256.toNat hx, hlocToNat]
  have nextPcLoc : nextPc = loc := nextPcEq.trans hxeq.symm
  cases nextPcLoc
  rcases subcode_of_get?_eq_some compiled hgetTable with
    ⟨jumpdestAt, bodySlice⟩
  have bodyBoundary := Prog.jumpable_of_get?_table compiled hgetTable
  rcases beforeJumpdestReached.advance_jumpToward jumpdestAt storeAt with
    ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
      jumpdestRun⟩
  rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
  subst bodyPc
  let bodyCursor : Exec.Deriv.SourceCursor root program ⟨index, []⟩ body :=
    ⟨_, _, bodyExec,
      cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
        |>.snoc jumpdestEdge,
      bodySlice, bodyBoundary.2, by
        intro site member
        simp only [Prog.sourceSites, List.mem_flatMap]
        refine ⟨index, ?_, ?_⟩
        · exact List.mem_range.mpr
            (List.getElem?_eq_some_iff.mp hgetBody).choose
        · simpa only [hgetTable] using member⟩
  have pushNotStore : ¬ Ninst.At root.sevm.code cursor.pc
      (.reg .sstore) := by
    intro storeHere
    have impossible := Ninst.at_unique storeHere pushAt
    cases impossible
  have jumpNotStore : ¬ Ninst.At root.sevm.code (cursor.pc + 3)
      (.reg .sstore) := by
    intro storeHere
    exact storeHere.false_of_jinstAt jumpAt
  have jumpdestNotStore : ¬ Ninst.At root.sevm.code loc
      (.reg .sstore) := by
    intro storeHere
    exact storeHere.false_of_jinstAt jumpdestAt
  let compilerPrefix : Exec.Deriv.ParentNonSstorePrefix
      cursor.node bodyCursor.node :=
    .step pushEdge pushNotStore
      (.step jumpEdge jumpNotStore
        (.step jumpdestEdge jumpdestNotStore (.refl _)))
  refine ⟨body, hgetBody, bodyCursor, compilerPrefix, bodyReached, ?_⟩
  exact Exec.Deriv.ParentNonSstorePrefix.lt_of_step
    pushEdge pushNotStore
    (.step jumpEdge jumpNotStore
      (.step jumpdestEdge jumpdestNotStore (.refl _)))

/-- Actual same-frame chronology around one source cursor retained by a
target-directed source traversal. -/
structure Exec.Deriv.SourceCursor.Chronology
    {root : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    (initial : Exec.Deriv.SourceCursor root program initialPath initialSource)
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (target : Exec.Deriv) where
  initialToCursor : Exec.Deriv.ParentPrefix initial.node cursor.node
  cursorToTarget : Exec.Deriv.ParentPrefix cursor.node target

/-- A retained cursor distinct from the target is strictly earlier in the
actual same-frame derivation.  `Exec.Deriv.lt` is descendant-first, so the
target occurs on the left of the conclusion. -/
theorem Exec.Deriv.SourceCursor.Chronology.strictBefore
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root program initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
    (distinct : cursor.node ≠ target) :
    Exec.Deriv.lt target cursor.node :=
  chronology.cursorToTarget.lt_of_ne distinct

/-- The actual target-directed compiler-source route to one reached non-PUSH
instruction.  Every constructor retains the current source cursor and both
sides of its execution chronology. Branches record the actually selected arm;
internal calls additionally retain the exact compiler-table lookup. -/
inductive Exec.Deriv.SourceCursor.Toward
    {root : Exec.Deriv} {program : Prog}
    {initialPath : Prog.SourcePath} {initialSource : Func}
    (initial : Exec.Deriv.SourceCursor root program initialPath initialSource)
    (target : Exec.Deriv) (targetInstruction : Ninst) :
    {path : Prog.SourcePath} → {source : Func} →
      Exec.Deriv.SourceCursor root program path source → Prop
  | atTarget {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
      (cursor : Exec.Deriv.SourceCursor root program path
        (.next instruction tail))
      (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
      (site : Prog.SourceSite)
      (siteEq : site =
        { path := path, pc := cursor.pc, instruction := instruction })
      (sourceMember : site ∈ program.sourceSites)
      (targetEq : cursor.node = target)
      (instructionEq : instruction = targetInstruction) :
      Exec.Deriv.SourceCursor.Toward initial target targetInstruction cursor
  | next {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
      (cursor : Exec.Deriv.SourceCursor root program path
        (.next instruction tail))
      (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
      (tailCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail)
      (edge : Exec.Deriv.ParentStep tailCursor.node cursor.node)
      (rest : Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction tailCursor) :
      Exec.Deriv.SourceCursor.Toward initial target targetInstruction cursor
  | branchLeft {path : Prog.SourcePath} {left right : Func}
      (cursor : Exec.Deriv.SourceCursor root program path (.branch left right))
      (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
      (arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left)
      (compilerPrefix :
        Exec.Deriv.ParentNonSstorePrefix cursor.node arm.node)
      (rest : Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction arm) :
      Exec.Deriv.SourceCursor.Toward initial target targetInstruction cursor
  | branchRight {path : Prog.SourcePath} {left right : Func}
      (cursor : Exec.Deriv.SourceCursor root program path (.branch left right))
      (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
      (arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right)
      (compilerPrefix :
        Exec.Deriv.ParentNonSstorePrefix cursor.node arm.node)
      (rest : Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction arm) :
      Exec.Deriv.SourceCursor.Toward initial target targetInstruction cursor
  | call {path : Prog.SourcePath} {index : Nat} {body : Func}
      (cursor : Exec.Deriv.SourceCursor root program path (.call index))
      (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
      (lookup : (program.main :: program.aux)[index]? = some body)
      (bodyCursor : Exec.Deriv.SourceCursor root program ⟨index, []⟩ body)
      (compilerPrefix :
        Exec.Deriv.ParentNonSstorePrefix cursor.node bodyCursor.node)
      (rest : Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction bodyCursor) :
      Exec.Deriv.SourceCursor.Toward initial target targetInstruction cursor

/-- The final cursor of an actual target-directed route recovers the existing
source-attribution result. -/
private theorem Exec.Deriv.SourceCursor.Toward.sourceSite
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {targetInstruction : Ninst}
    {initial : Exec.Deriv.SourceCursor root program initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = targetInstruction := by
  induction route with
  | atTarget cursor chronology site siteEq sourceMember targetEq instructionEq =>
      refine ⟨site, sourceMember, ?_, ?_⟩
      · have pcEq := congrArg Exec.Deriv.pc targetEq
        simpa [Exec.Deriv.SourceCursor.node, siteEq] using pcEq
      · simpa [siteEq] using instructionEq
  | next cursor chronology tailCursor edge rest ih => exact ih
  | branchLeft cursor chronology arm compilerPrefix rest ih => exact ih
  | branchRight cursor chronology arm compilerPrefix rest ih => exact ih
  | call cursor chronology lookup bodyCursor compilerPrefix rest ih => exact ih

/-- Expose the source-site result of a completed target-directed route without
exposing the traversal's private induction kernel. -/
theorem Exec.Deriv.SourceCursor.Toward.sourceSiteResult
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {targetInstruction : Ninst}
    {initial : Exec.Deriv.SourceCursor root program initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = targetInstruction := by
  exact route.sourceSite

/-- The sole target-directed source traversal follows the finite execution
proof, not the source call graph, and retains every intermediate cursor. -/
private theorem Exec.Deriv.SourceCursor.toward_core :
    ∀ current : Exec.Deriv,
      ∀ {root : Exec.Deriv} {program : Prog}
        {initialPath path : Prog.SourcePath}
        {initialSource source : Func}
        {targetInstruction : Ninst} {target : Exec.Deriv}
        (initial : Exec.Deriv.SourceCursor root program
          initialPath initialSource)
        (cursor : Exec.Deriv.SourceCursor root program path source),
        cursor.node = current →
        some root.sevm.code.toList = program.compile →
        Exec.Deriv.SourceCursor.Chronology initial cursor target →
        NinstNonPush targetInstruction →
        Ninst.At target.sevm.code target.pc targetInstruction →
        Exec.Deriv.SourceCursor.Toward
          initial target targetInstruction cursor := by
  let property : Exec.Deriv.Pred := fun current =>
    ∀ {root : Exec.Deriv} {program : Prog}
      {initialPath path : Prog.SourcePath}
      {initialSource source : Func}
      {targetInstruction : Ninst} {target : Exec.Deriv}
      (initial : Exec.Deriv.SourceCursor root program
        initialPath initialSource)
      (cursor : Exec.Deriv.SourceCursor root program path source),
      cursor.node = current →
      some root.sevm.code.toList = program.compile →
      Exec.Deriv.SourceCursor.Chronology initial cursor target →
      NinstNonPush targetInstruction →
      Ninst.At target.sevm.code target.pc targetInstruction →
      Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction cursor
  apply Exec.Deriv.strongRec property
  intro current ih root program initialPath path initialSource source
    targetInstruction target initial cursor hcurrent compiled chronology
    targetNonPush instructionAt
  subst current
  cases source with
  | last outcome =>
      have lastAt : Linst.At root.sevm.code cursor.pc outcome :=
        Linst.at_of_slice cursor.codeSlice
      cases chronology.cursorToTarget with
      | refl => exact (instructionAt.false_of_linstAt lastAt).elim
      | step edge suffix => exact (edge.false_of_linstAt lastAt).elim
  | next instruction tail =>
      cases chronology.cursorToTarget with
      | refl =>
          let site : Prog.SourceSite :=
            { path := path, pc := cursor.pc, instruction := instruction }
          have localMember : site ∈
              Func.sourceSites path.functionIndex path.steps cursor.pc
                (.next instruction tail) := by
            rcases path with ⟨functionIndex, steps⟩
            simp [site, Func.sourceSites]
          have sourceAt : Ninst.At root.sevm.code cursor.pc instruction :=
            Func.sourceSites_sound cursor.codeSlice cursor.codeBoundary
              localMember
          have instructionEq := Ninst.at_unique sourceAt instructionAt
          exact .atTarget cursor chronology site rfl
            (cursor.sourceIncluded localMember) rfl instructionEq
      | step occurrenceEdge suffix =>
          rcases cursor.nextOfParentStep occurrenceEdge with
            ⟨tailCursor, tailNodeEq⟩
          have tailEdge : Exec.Deriv.ParentStep
              tailCursor.node cursor.node := by
            rw [tailNodeEq]
            exact occurrenceEdge
          have tailReached :
              Exec.Deriv.ParentPrefix tailCursor.node target := by
            rw [tailNodeEq]
            exact suffix
          let tailChronology :
              Exec.Deriv.SourceCursor.Chronology
                initial tailCursor target :=
            ⟨chronology.initialToCursor.trans
                (.step tailEdge (.refl _)),
              tailReached⟩
          have rest := ih tailCursor.node tailEdge.lt initial tailCursor rfl
            compiled tailChronology targetNonPush instructionAt
          exact .next cursor chronology tailCursor tailEdge rest
  | branch left right =>
      rcases cursor.branchToward chronology.cursorToTarget
          targetNonPush instructionAt with
        ⟨arm, compilerPrefix, armReached, decrease⟩ |
        ⟨arm, compilerPrefix, armReached, decrease⟩
      · let armChronology :
            Exec.Deriv.SourceCursor.Chronology initial arm target :=
          ⟨chronology.initialToCursor.trans
              compilerPrefix.toParentPrefix,
            armReached⟩
        have rest := ih arm.node decrease initial arm rfl compiled
          armChronology targetNonPush instructionAt
        exact .branchLeft cursor chronology arm compilerPrefix rest
      · let armChronology :
            Exec.Deriv.SourceCursor.Chronology initial arm target :=
          ⟨chronology.initialToCursor.trans
              compilerPrefix.toParentPrefix,
            armReached⟩
        have rest := ih arm.node decrease initial arm rfl compiled
          armChronology targetNonPush instructionAt
        exact .branchRight cursor chronology arm compilerPrefix rest
  | call index =>
      rcases cursor.callToward compiled chronology.cursorToTarget
          targetNonPush instructionAt with
        ⟨body, lookup, bodyCursor, compilerPrefix, bodyReached, decrease⟩
      let bodyChronology :
          Exec.Deriv.SourceCursor.Chronology initial bodyCursor target :=
        ⟨chronology.initialToCursor.trans
            compilerPrefix.toParentPrefix,
          bodyReached⟩
      have rest := ih bodyCursor.node decrease initial bodyCursor rfl compiled
        bodyChronology targetNonPush instructionAt
      exact .call cursor chronology lookup bodyCursor compilerPrefix rest

/-- Public actual target-directed route for any reached non-PUSH source
instruction in an arbitrary-outcome raw source cursor. -/
theorem Exec.Deriv.SourceCursor.toward
    {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func} {instruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    Exec.Deriv.SourceCursor.Toward cursor target instruction cursor := by
  let chronology : Exec.Deriv.SourceCursor.Chronology cursor cursor target :=
    ⟨.refl _, reached⟩
  exact Exec.Deriv.SourceCursor.toward_core cursor.node cursor cursor rfl
    compiled chronology nonPush instructionAt

/-- Public target-directed completeness for any reached non-PUSH source
instruction in an arbitrary-outcome raw source cursor. -/
theorem Exec.Deriv.SourceCursor.sourceSite
    {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func} {instruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = instruction := by
  exact (cursor.toward compiled reached nonPush instructionAt).sourceSite

/-- Public target-directed completeness for an arbitrary-outcome raw source
cursor. -/
theorem Exec.Deriv.SourceCursor.sstoreSite
    {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = .reg .sstore := by
  exact cursor.sourceSite compiled reached (by trivial) storeAt

/-- Exact-invocation completeness for every actually reached same-frame
non-PUSH source instruction. -/
theorem Exec.Deriv.nonPush_sourceSite
    {root target : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr} {instruction : Ninst}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = instruction := by
  rcases Exec.Deriv.SourceCursor.mainToward invocation sameFrame instructionAt with
    ⟨mainCursor, compilerPrefix, reached⟩
  exact mainCursor.sourceSite invocation.2.2.2 reached nonPush instructionAt

/-- Exact-invocation completeness for every actually reached same-frame
SSTORE, with no outcome or commitment premise. -/
theorem Exec.Deriv.sstore_sourceSite
    {root target : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = .reg .sstore := by
  exact root.nonPush_sourceSite invocation sameFrame (by trivial) storeAt

/-- Successful-step specialization over an arbitrary-outcome raw root.  The
enclosing frame may still fail or later roll back. -/
theorem Exec.Deriv.successfulSstore_sourceSite
    {root : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (write : Exec.SuccessfulSstoreOccurrence root)
    (sameFrame : Exec.Deriv.ParentPrefix root write.occurrence.node) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = write.occurrence.node.pc ∧
      site.instruction = .reg .sstore := by
  have storeAt : Ninst.At write.occurrence.node.sevm.code
      write.occurrence.node.pc (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  exact root.sstore_sourceSite invocation sameFrame storeAt

/-- Every global instruction occurrence selects at least one actual raw frame
root whose same-frame prefix contains its proof node.  No uniqueness of roots
or list positions is claimed. -/
theorem Exec.NinstOccurrence.exists_rawFrameRoot_parentPrefix
    {globalRoot : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence globalRoot) :
    ∃ frameRoot ∈ Exec.rawFrameRoots globalRoot.exc,
      Exec.Deriv.ParentPrefix frameRoot occurrence.node :=
  (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix
    globalRoot.exc occurrence.node).mp occurrence.reached

/-- Quantified all-frame attribution: a selected raw traversal root supplies
source provenance exactly when that root has the nominated compiled identity
and owns the occurrence through a same-frame prefix. -/
theorem Exec.NinstOccurrence.sourceSite_of_rawFrameRoot
    {globalRoot frameRoot : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (_selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : frameRoot.exactInvocation program storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix frameRoot occurrence.node) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = occurrence.node.pc ∧
      site.instruction = .reg .sstore := by
  have storeAt : Ninst.At occurrence.node.sevm.code occurrence.node.pc
      (.reg .sstore) := by
    rw [← instructionEq]
    exact occurrence.decoded
  exact frameRoot.sstore_sourceSite invocation sameFrame storeAt

/-- Proof cursor connecting one actually reached same-frame node to one
compiler source body.  `sourceIncluded` embeds its local executable sites into
the whole-program map and is preserved while following the finite execution
prefix, including recursive internal calls. -/
structure Exec.Frame.SourceCursor
    (frame : Exec.Frame) (program : Prog)
    (path : Prog.SourcePath) (source : Func) where
  pc : Nat
  pre : Devm
  current : Exec pc frame.sevm pre frame.out
  parentPrefix : Exec.Deriv.ParentPrefix frame.rootDeriv
    ⟨pc, frame.sevm, pre, frame.out, current⟩
  codeSlice : subcode frame.sevm.code.toList pc
    (Func.compile (table 0 (program.main :: program.aux)) pc source)
  codeBoundary : noPushBefore frame.sevm.code pc 32 = true
  sourceIncluded : ∀ {site},
    site ∈ Func.sourceSites path.functionIndex path.steps pc source →
      site ∈ program.sourceSites

/-- The exact reached derivation selected by a source cursor. -/
def Exec.Frame.SourceCursor.node
    {frame : Exec.Frame} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Frame.SourceCursor frame program path source) : Exec.Deriv :=
  ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩

/-- View the landed committed-frame cursor through the canonical raw cursor.
The commit witness contributes no navigation or source-map data. -/
def Exec.Frame.SourceCursor.toRaw
    {frame : Exec.Frame} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Frame.SourceCursor frame program path source) :
    Exec.Deriv.SourceCursor frame.rootDeriv program path source :=
  ⟨cursor.pc, cursor.pre, cursor.current, cursor.parentPrefix,
    cursor.codeSlice, cursor.codeBoundary, cursor.sourceIncluded⟩

@[simp] theorem Exec.Frame.SourceCursor.toRaw_node
    {frame : Exec.Frame} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Frame.SourceCursor frame program path source) :
    cursor.toRaw.node = cursor.node := by
  rfl

/-- Enter the main source body through the compiler's leading `JUMPDEST`. -/
theorem Exec.Frame.SourceCursor.main
    {frame : Exec.Frame} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : frame.exactInvocation program storageTarget codeAddress) :
    ∃ cursor : Exec.Frame.SourceCursor frame program ⟨0, []⟩ program.main,
      Exec.Deriv.ParentNonSstorePrefix frame.rootDeriv
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ := by
  rcases frame with ⟨pc, sevm, pre, out, run, committed⟩
  rcases invocation with ⟨hpc, htarget, haddress, hcode⟩
  dsimp at hpc htarget haddress hcode
  subst pc
  cases out with
  | error error =>
      simp [Execution.commits] at committed
  | ok post =>
      have hget :
          (table 0 (program.main :: program.aux))[0]? =
            some (0, program.main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with
        ⟨jumpdestAt, sourceSlice⟩
      have sourceBoundary : noPushBefore sevm.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run jumpdestAt with
        ⟨inter, current, burn, hgas, prec⟩
      have entryStep : Evm.step ⟨0, sevm, pre⟩ = .cont 1 inter :=
        Evm.jumpdest_cont jumpdestAt (Devm.BurnBy.of_burn burn hgas)
      have runEq : run = .cont entryStep current := Exec.unique _ _
      have parentPrefix : Exec.Deriv.ParentPrefix
          (Exec.Frame.rootDeriv ⟨0, sevm, pre, .ok post, run, committed⟩)
          ⟨1, sevm, inter, .ok post, current⟩ := by
        rw [runEq]
        exact .step (.cont entryStep current) (.refl _)
      let edge : Exec.Deriv.ParentStep
          ⟨1, sevm, inter, .ok post, current⟩
          (Exec.Frame.rootDeriv
            ⟨0, sevm, pre, .ok post, run, committed⟩) := by
        rw [runEq]
        exact .cont entryStep current
      have notStore : ¬ Ninst.At sevm.code 0 (.reg .sstore) := by
        intro storeAt
        exact storeAt.false_of_jinstAt jumpdestAt
      refine ⟨⟨1, inter, current, parentPrefix, sourceSlice,
        sourceBoundary, ?_⟩, .step edge notStore (.refl _)⟩
      intro site member
      simp only [Prog.sourceSites, List.mem_flatMap]
      refine ⟨0, by simp, ?_⟩
      simpa only [hget] using member

/-- Advance over one actually successful source `.next` instruction. -/
theorem Exec.Frame.SourceCursor.next
    {frame : Exec.Frame} {program : Prog}
    {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
    (cursor : Exec.Frame.SourceCursor frame program path
      (.next instruction tail)) :
    ∃ nextCursor : Exec.Frame.SourceCursor frame program
        ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail,
      Exec.Deriv.ParentStep
        ⟨nextCursor.pc, frame.sevm, nextCursor.pre, frame.out,
          nextCursor.current⟩
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ := by
  rcases frame with ⟨rootPc, sevm, rootPre, out, rootRun, committed⟩
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok final =>
      have sourceAt : Ninst.At sevm.code cursor.pc instruction :=
        Func.sourceSites_sound cursor.codeSlice cursor.codeBoundary
          (functionIndex := path.functionIndex) (steps := path.steps)
          (site := { path := path, pc := cursor.pc, instruction := instruction })
          (by rcases path with ⟨functionIndex, steps⟩
              simp [Func.sourceSites])
      rcases Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary with
        ⟨tailBoundary, tailSlice⟩
      cases hcurrent : cursor.current with
      | halt step =>
          exact (Ninst.step_ne_halt_ok
            ((Evm.step_next sourceAt).symm.trans step)).elim
      | cont step next =>
          have sourceStep := (Evm.step_next sourceAt).symm.trans step
          cases Ninst.step_cont_pc sourceStep
          let edge : Exec.Deriv.ParentStep
              ⟨cursor.pc + instruction.size, sevm, _, .ok final, next⟩
              ⟨cursor.pc, sevm, cursor.pre, .ok final, .cont step next⟩ :=
            .cont step next
          have oldPrefix := cursor.parentPrefix
          rw [hcurrent] at oldPrefix
          have nextPrefix := oldPrefix.snoc edge
          refine ⟨⟨_, _, next, nextPrefix,
            tailSlice, tailBoundary, ?_⟩, edge⟩
          intro site member
          apply cursor.sourceIncluded
          simp [Func.sourceSites, member]
      | doneOk step enter resume next =>
          have sourceStep := (Evm.step_next sourceAt).symm.trans step
          cases Ninst.step_spawn_pc sourceStep
          let edge : Exec.Deriv.ParentStep
              ⟨cursor.pc + instruction.size, sevm, _, .ok final, next⟩
              ⟨cursor.pc, sevm, cursor.pre, .ok final,
                .doneOk step enter resume next⟩ :=
            .doneOk step enter resume next
          have oldPrefix := cursor.parentPrefix
          rw [hcurrent] at oldPrefix
          have nextPrefix := oldPrefix.snoc edge
          refine ⟨⟨_, _, next, nextPrefix,
            tailSlice, tailBoundary, ?_⟩, edge⟩
          intro site member
          apply cursor.sourceIncluded
          simp [Func.sourceSites, member]
      | runOk step enter child resume next =>
          have sourceStep := (Evm.step_next sourceAt).symm.trans step
          cases Ninst.step_spawn_pc sourceStep
          let edge : Exec.Deriv.ParentStep
              ⟨cursor.pc + instruction.size, sevm, _, .ok final, next⟩
              ⟨cursor.pc, sevm, cursor.pre, .ok final,
                .runOk step enter child resume next⟩ :=
            .runOk step enter child resume next
          have oldPrefix := cursor.parentPrefix
          rw [hcurrent] at oldPrefix
          have nextPrefix := oldPrefix.snoc edge
          refine ⟨⟨_, _, next, nextPrefix,
            tailSlice, tailBoundary, ?_⟩, edge⟩
          intro site member
          apply cursor.sourceIncluded
          simp [Func.sourceSites, member]

/-- Select the source branch arm followed by the actual successful execution,
crossing only the compiler's PUSH/JUMPI/JUMPDEST glue. -/
theorem Exec.Frame.SourceCursor.branch
    {frame : Exec.Frame} {program : Prog} {path : Prog.SourcePath}
    {left right : Func}
    (cursor : Exec.Frame.SourceCursor frame program path
      (.branch left right)) :
    (∃ arm : Exec.Frame.SourceCursor frame program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.ParentNonSstorePrefix
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
        ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩ ∧
      Exec.Deriv.lt
        ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩) ∨
    (∃ arm : Exec.Frame.SourceCursor frame program
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
      Exec.Deriv.ParentNonSstorePrefix
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
        ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩ ∧
      Exec.Deriv.lt
        ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩) := by
  rcases frame with ⟨rootPc, sevm, rootPre, out, rootRun, committed⟩
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok final =>
      rcases subcode_compile_branch_jumpable cursor.codeSlice
          cursor.codeBoundary with
        ⟨loc, hlocEq, hloc, pushAt, jumpiAt, leftSlice, leftBoundary,
          jumpdestAt, jumpable, rightSlice, rightBoundary⟩
      rcases pushAt_exact cursor.current ⟨_, pushAt⟩ (by simp) with
        ⟨afterPushPre, afterPush, pushBurn, room, pushGas, pushPrec⟩
      rw [List.toB256_pair _ hloc] at pushBurn
      rcases jumpi_at_exact afterPush jumpiAt with
        ⟨x, armPre, armExec, popBurn, jumpGas, jumpPrec⟩ |
        ⟨x, flag, beforeJumpdestPre, beforeJumpdest, popBurn, jumpGas,
          actualJumpable, nonzero, jumpPrec⟩
      · have combined : Devm.PopBurn [0] cursor.pre armPre := by
          rcases (Devm.pushBurn_cons_popBurn_cons pushBurn popBurn).right with
            ⟨stack, pushBurn', popBurn'⟩
          exact Devm.popBurn_of_burn_of_popBurn
            (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
        have steps := Evm.branch_zero_steps pushAt jumpiAt hloc room
          (Devm.PopBurnBy.of_popBurn combined (by omega))
        rcases cursor.parentPrefix.advance_cont cursor.current steps.1 with
          ⟨afterPush', pushEdge, afterPushPrefix⟩
        rcases afterPushPrefix.advance_cont afterPush' steps.2 with
          ⟨armExec', jumpEdge, armPrefix⟩
        let armCursor : Exec.Frame.SourceCursor
            ⟨rootPc, sevm, rootPre, .ok final, rootRun, committed⟩ program
            ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left :=
          ⟨_, _, armExec', armPrefix, leftSlice, leftBoundary, by
            intro site member
            apply cursor.sourceIncluded
            simp only [Func.sourceSites, List.mem_append]
            exact Or.inl member⟩
        have pushNotStore : ¬ Ninst.At sevm.code cursor.pc (.reg .sstore) := by
          intro storeAt
          have impossible := Ninst.at_unique storeAt pushAt
          cases impossible
        have jumpNotStore : ¬ Ninst.At sevm.code (cursor.pc + 3)
            (.reg .sstore) := by
          intro storeAt
          exact storeAt.false_of_jinstAt jumpiAt
        let compilerPrefix : Exec.Deriv.ParentNonSstorePrefix
            ⟨cursor.pc, sevm, cursor.pre, .ok final, cursor.current⟩
            ⟨armCursor.pc, sevm, armCursor.pre, .ok final,
              armCursor.current⟩ :=
          .step pushEdge pushNotStore
            (.step jumpEdge jumpNotStore (.refl _))
        refine Or.inl ⟨armCursor, compilerPrefix, ?_⟩
        exact Exec.Deriv.ParentNonSstorePrefix.lt_of_step
          pushEdge pushNotStore
          (.step jumpEdge jumpNotStore (.refl _))
      · have hloc256 : loc < 2 ^ 256 := by
          apply Nat.lt_trans hloc
          rw [Nat.pow_lt_pow_iff_right] <;> omega
        have combined : loc = x.toNat ∧
            Devm.PopBurn [flag] cursor.pre beforeJumpdestPre := by
          rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
            ⟨hx, stack, pushBurn', popBurn'⟩
          have hlocToNat : loc.toB256.toNat = loc :=
            B256.toNat_toB256_of_lt hloc256
          rw [← congrArg B256.toNat hx, hlocToNat]
          exact ⟨rfl, Devm.popBurn_of_burn_of_popBurn
            (Devm.burn_of_pushBurn_nil pushBurn') popBurn'⟩
        rcases combined with ⟨hxeq, combined⟩
        have jumpdestAtX := jumpdestAt
        rw [hxeq] at jumpdestAtX
        rcases jumpdest_at_exact beforeJumpdest jumpdestAtX with
          ⟨armPre, armExec, jumpdestBurn, jumpdestGas, jumpdestPrec⟩
        have combined' : Devm.PopBurn [flag] cursor.pre armPre :=
          Devm.popBurn_of_popBurn_of_pop combined jumpdestBurn
        have totalGas : cursor.pre.gasLeft =
            armPre.gasLeft + (gVerylow + gHigh + gJumpdest) := by omega
        have steps := Evm.branch_succ_steps pushAt jumpiAt jumpdestAt
          jumpable hloc nonzero room
          (Devm.PopBurnBy.of_popBurn combined' totalGas)
        rcases cursor.parentPrefix.advance_cont cursor.current steps.1 with
          ⟨afterPush', pushEdge, afterPushPrefix⟩
        rcases afterPushPrefix.advance_cont afterPush' steps.2.1 with
          ⟨beforeJumpdest', jumpEdge, beforeJumpdestPrefix⟩
        rcases beforeJumpdestPrefix.advance_cont beforeJumpdest'
            steps.2.2 with
          ⟨armExec', jumpdestEdge, armPrefix⟩
        let armCursor : Exec.Frame.SourceCursor
            ⟨rootPc, sevm, rootPre, .ok final, rootRun, committed⟩ program
            ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right :=
          ⟨_, _, armExec', armPrefix, rightSlice, rightBoundary, by
            intro site member
            apply cursor.sourceIncluded
            simp only [Func.sourceSites, List.mem_append]
            apply Or.inr
            have hrightPc : loc + 1 = cursor.pc + compsize left + 5 := by omega
            rw [← hrightPc]
            exact member⟩
        have pushNotStore : ¬ Ninst.At sevm.code cursor.pc (.reg .sstore) := by
          intro storeAt
          have impossible := Ninst.at_unique storeAt pushAt
          cases impossible
        have jumpNotStore : ¬ Ninst.At sevm.code (cursor.pc + 3)
            (.reg .sstore) := by
          intro storeAt
          exact storeAt.false_of_jinstAt jumpiAt
        have jumpdestNotStore : ¬ Ninst.At sevm.code loc
            (.reg .sstore) := by
          intro storeAt
          exact storeAt.false_of_jinstAt jumpdestAt
        let compilerPrefix : Exec.Deriv.ParentNonSstorePrefix
            ⟨cursor.pc, sevm, cursor.pre, .ok final, cursor.current⟩
            ⟨armCursor.pc, sevm, armCursor.pre, .ok final,
              armCursor.current⟩ :=
          .step pushEdge pushNotStore
            (.step jumpEdge jumpNotStore
              (.step jumpdestEdge jumpdestNotStore (.refl _)))
        refine Or.inr ⟨armCursor, compilerPrefix, ?_⟩
        exact Exec.Deriv.ParentNonSstorePrefix.lt_of_step
          pushEdge pushNotStore
          (.step jumpEdge jumpNotStore
            (.step jumpdestEdge jumpdestNotStore (.refl _)))

/-- Follow one actually executed internal source call to its table body.  The
proof consumes exactly the PUSH/JUMP/JUMPDEST prefix and does not recurse over
the source call graph. -/
theorem Exec.Frame.SourceCursor.call
    {frame : Exec.Frame} {program : Prog} {path : Prog.SourcePath}
    {index : Nat}
    (cursor : Exec.Frame.SourceCursor frame program path (.call index))
    (compiled : some frame.sevm.code.toList = program.compile) :
    ∃ body, (program.main :: program.aux)[index]? = some body ∧
      ∃ bodyCursor : Exec.Frame.SourceCursor frame program ⟨index, []⟩ body,
        Exec.Deriv.ParentNonSstorePrefix
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          ⟨bodyCursor.pc, frame.sevm, bodyCursor.pre, frame.out,
            bodyCursor.current⟩ ∧
        Exec.Deriv.lt
          ⟨bodyCursor.pc, frame.sevm, bodyCursor.pre, frame.out,
            bodyCursor.current⟩
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ := by
  rcases frame with ⟨rootPc, sevm, rootPre, out, rootRun, committed⟩
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok final =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, body, hgetTable, hloc, pushAt, jumpAt⟩
      rcases pushAt with ⟨pushLe, pushAt⟩
      have hgetBody : (program.main :: program.aux)[index]? = some body := by
        have h := @Prog.get?_table 0 index (program.main :: program.aux)
        rw [hgetTable] at h
        simpa using h.symm
      rcases pushAt_exact cursor.current ⟨pushLe, pushAt⟩ (by simp) with
        ⟨afterPushPre, afterPush, pushBurn, room, pushGas, pushPrec⟩
      rw [List.toB256_pair _ hloc] at pushBurn
      rcases jump_at_exact afterPush jumpAt with
        ⟨x, beforeJumpdestPre, beforeJumpdest, popBurn, jumpGas,
          actualJumpable, jumpPrec⟩
      have hloc256 : loc < 2 ^ 256 := by
        apply Nat.lt_trans hloc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have combined : loc = x.toNat ∧
          Devm.Burn cursor.pre beforeJumpdestPre := by
        rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
          ⟨hx, stack, pushBurn', popBurn'⟩
        have hlocToNat : loc.toB256.toNat = loc :=
          B256.toNat_toB256_of_lt hloc256
        rw [← congrArg B256.toNat hx, hlocToNat]
        exact ⟨rfl, Devm.burn_trans
          (Devm.burn_of_pushBurn_nil pushBurn')
          (Devm.burn_of_popBurn_nil popBurn')⟩
      rcases combined with ⟨hxeq, combined⟩
      rcases subcode_of_get?_eq_some compiled hgetTable with
        ⟨jumpdestAt, bodySlice⟩
      have targetJumpable := Prog.jumpable_of_get?_table compiled hgetTable
      have jumpdestAtX := jumpdestAt
      rw [hxeq] at jumpdestAtX
      rcases jumpdest_at_exact beforeJumpdest jumpdestAtX with
        ⟨bodyPre, bodyExec, jumpdestBurn, jumpdestGas, jumpdestPrec⟩
      have totalBurn : Devm.Burn cursor.pre bodyPre :=
        Devm.burn_trans combined jumpdestBurn
      have totalGas : cursor.pre.gasLeft =
          bodyPre.gasLeft + (gVerylow + gMid + gJumpdest) := by omega
      have steps := Evm.call_steps (le := pushLe) pushAt jumpAt
        jumpdestAt targetJumpable.1 hloc room
        (Devm.BurnBy.of_burn totalBurn totalGas)
      rcases cursor.parentPrefix.advance_cont cursor.current steps.1 with
        ⟨afterPush', pushEdge, afterPushPrefix⟩
      rcases afterPushPrefix.advance_cont afterPush' steps.2.1 with
        ⟨beforeJumpdest', jumpEdge, beforeJumpdestPrefix⟩
      rcases beforeJumpdestPrefix.advance_cont beforeJumpdest' steps.2.2 with
        ⟨bodyExec', jumpdestEdge, bodyPrefix⟩
      let bodyCursor : Exec.Frame.SourceCursor
          ⟨rootPc, sevm, rootPre, .ok final, rootRun, committed⟩ program
          ⟨index, []⟩ body :=
        ⟨_, _, bodyExec', bodyPrefix, bodySlice, targetJumpable.2, by
          intro site member
          simp only [Prog.sourceSites, List.mem_flatMap]
          refine ⟨index, ?_, ?_⟩
          · exact List.mem_range.mpr
              (List.getElem?_eq_some_iff.mp hgetBody).choose
          · simpa only [hgetTable] using member⟩
      have pushNotStore : ¬ Ninst.At sevm.code cursor.pc (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.at_unique storeAt pushAt
        cases impossible
      have jumpNotStore : ¬ Ninst.At sevm.code (cursor.pc + 3)
          (.reg .sstore) := by
        intro storeAt
        exact storeAt.false_of_jinstAt jumpAt
      have jumpdestNotStore : ¬ Ninst.At sevm.code loc
          (.reg .sstore) := by
        intro storeAt
        exact storeAt.false_of_jinstAt jumpdestAt
      let compilerPrefix : Exec.Deriv.ParentNonSstorePrefix
          ⟨cursor.pc, sevm, cursor.pre, .ok final, cursor.current⟩
          ⟨bodyCursor.pc, sevm, bodyCursor.pre, .ok final,
            bodyCursor.current⟩ :=
        .step pushEdge pushNotStore
          (.step jumpEdge jumpNotStore
            (.step jumpdestEdge jumpdestNotStore (.refl _)))
      refine ⟨body, hgetBody, bodyCursor, compilerPrefix, ?_⟩
      exact Exec.Deriv.ParentNonSstorePrefix.lt_of_step
        pushEdge pushNotStore
        (.step jumpEdge jumpNotStore
          (.step jumpdestEdge jumpdestNotStore (.refl _)))

/-- Public cursor completeness for successful SSTORE source attribution. -/
theorem Exec.Frame.SourceCursor.sstoreSite
    {frame : Exec.Frame} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Frame.SourceCursor frame program path source)
    (compiled : some frame.sevm.code.toList = program.compile)
    (write : Exec.SuccessfulSstoreOccurrence frame.rootDeriv)
    (reached : Exec.Deriv.ParentPrefix cursor.node write.occurrence.node) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = write.occurrence.node.pc ∧
      site.instruction = .reg .sstore := by
  have storeAt : Ninst.At write.occurrence.node.sevm.code
      write.occurrence.node.pc (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  simpa only [Exec.Frame.SourceCursor.toRaw_node] using
    cursor.toRaw.sstoreSite compiled reached storeAt

/-- Exact-invocation completeness: every same-frame successful SSTORE has an
exact structural source site in the executable compiler map. -/
theorem Exec.Frame.successfulSstore_sourceSite
    {frame : Exec.Frame} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : frame.exactInvocation program storageTarget codeAddress)
    (write : Exec.SuccessfulSstoreOccurrence frame.rootDeriv)
    (sameFrame : Exec.Deriv.ParentPrefix frame.rootDeriv
      write.occurrence.node) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = write.occurrence.node.pc ∧
      site.instruction = .reg .sstore := by
  have storeAt : Ninst.At write.occurrence.node.sevm.code
      write.occurrence.node.pc (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  exact frame.rootDeriv.sstore_sourceSite
    (frame.exactInvocation_iff_rootDeriv.mp invocation) sameFrame storeAt

/-! ## Executable SSTORE source checker -/

/-- Executable exact match for one structural SSTORE site. -/
def Prog.SourceSite.matchesSstore
    (site : Prog.SourceSite) (path : Prog.SourcePath) (pc : Nat) : Bool :=
  site.path == path && site.pc == pc &&
    match site.instruction with
    | .reg .sstore => true
    | _ => false

@[simp] theorem Prog.SourceSite.matchesSstore_eq_true
    {site : Prog.SourceSite} {path : Prog.SourcePath} {pc : Nat} :
    site.matchesSstore path pc = true ↔
      site.path = path ∧ site.pc = pc ∧
        site.instruction = .reg .sstore := by
  rcases site with ⟨sitePath, sitePc, instruction⟩
  cases instruction <;> simp [Prog.SourceSite.matchesSstore]
  rename_i regular
  cases regular <;> simp

/-- Decide whether a structural path and compiled PC name a source SSTORE. -/
def Prog.acceptsSstoreSite
    (program : Prog) (path : Prog.SourcePath) (pc : Nat) : Bool :=
  program.sourceSites.any fun site => site.matchesSstore path pc

/-- Logical specification of the executable SSTORE-site checker. -/
theorem Prog.acceptsSstoreSite_iff
    {program : Prog} {path : Prog.SourcePath} {pc : Nat} :
    program.acceptsSstoreSite path pc = true ↔
      ∃ site ∈ program.sourceSites,
        site.path = path ∧ site.pc = pc ∧
          site.instruction = .reg .sstore := by
  simp [Prog.acceptsSstoreSite]

/-- Checker acceptance decodes the exact SSTORE byte at the requested PC. -/
theorem Prog.acceptsSstoreSite_sound
    {program : Prog} {code : ByteArray}
    {path : Prog.SourcePath} {pc : Nat}
    (compiled : some code.toList = program.compile)
    (accepted : program.acceptsSstoreSite path pc = true) :
    Ninst.At code pc (.reg .sstore) := by
  rcases Prog.acceptsSstoreSite_iff.mp accepted with
    ⟨site, member, hpath, hpc, hinstruction⟩
  simpa only [hpc, hinstruction] using program.sourceSites_sound compiled member

/-- Executable checker form of exact same-frame SSTORE attribution for an
arbitrary-outcome raw root. -/
theorem Exec.Deriv.sstore_acceptsSource
    {root target : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ path : Prog.SourcePath,
      program.acceptsSstoreSite path target.pc = true := by
  rcases root.sstore_sourceSite invocation sameFrame storeAt with
    ⟨site, member, hpc, hinstruction⟩
  exact ⟨site.path, Prog.acceptsSstoreSite_iff.mpr
    ⟨site, member, rfl, hpc, hinstruction⟩⟩

/-- Global-occurrence form of the all-frame executable attribution bridge. -/
theorem Exec.NinstOccurrence.acceptsSource_of_rawFrameRoot
    {globalRoot frameRoot : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : frameRoot.exactInvocation program storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix frameRoot occurrence.node) :
    ∃ path : Prog.SourcePath,
      program.acceptsSstoreSite path occurrence.node.pc = true := by
  rcases occurrence.sourceSite_of_rawFrameRoot instructionEq selected invocation
      sameFrame with ⟨site, member, hpc, hinstruction⟩
  exact ⟨site.path, Prog.acceptsSstoreSite_iff.mpr
    ⟨site, member, rfl, hpc, hinstruction⟩⟩

/-- Every same-frame successful SSTORE from an exact invocation is accepted
at its exact structural path and PC. -/
theorem Exec.Frame.successfulSstore_acceptsSource
    {frame : Exec.Frame} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : frame.exactInvocation program storageTarget codeAddress)
    (write : Exec.SuccessfulSstoreOccurrence frame.rootDeriv)
    (sameFrame : Exec.Deriv.ParentPrefix frame.rootDeriv
      write.occurrence.node) :
    ∃ path : Prog.SourcePath,
      program.acceptsSstoreSite path write.occurrence.node.pc = true := by
  rcases frame.successfulSstore_sourceSite invocation write sameFrame with
    ⟨site, member, hpc, hinstruction⟩
  exact ⟨site.path, Prog.acceptsSstoreSite_iff.mpr
    ⟨site, member, rfl, hpc, hinstruction⟩⟩

end Blanc
