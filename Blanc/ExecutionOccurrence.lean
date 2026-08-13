import Blanc.ExecutionSettlement
import Blanc.Compiled
import Blanc.CommonProofs
import Blanc.ExecDeterminism

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

@[simp] theorem table_length (start : Nat) (functions : List Func) :
    (table start functions).length = functions.length := by
  induction functions generalizing start with
  | nil => rfl
  | cons head tail ih => simp [table, ih]

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

/-- An actually reached successful SSTORE in a compiler cursor is represented
by an exact source site.  Recursion follows the finite execution derivation,
not the source call graph. -/
private theorem Exec.Frame.SourceCursor.sstoreSite_core :
    ∀ current : Exec.Deriv,
      ∀ {frame : Exec.Frame} {program : Prog}
        {path : Prog.SourcePath} {source : Func}
        (cursor : Exec.Frame.SourceCursor frame program path source),
        cursor.node = current →
        some frame.sevm.code.toList = program.compile →
        ∀ (target : Exec.Deriv),
          Exec.Deriv.ParentPrefix cursor.node target →
          Ninst.At target.sevm.code target.pc (.reg .sstore) →
          ∃ site : Prog.SourceSite,
            site ∈ program.sourceSites ∧
            site.pc = target.pc ∧
            site.instruction = .reg .sstore := by
  let property : Exec.Deriv.Pred := fun current =>
    ∀ {frame : Exec.Frame} {program : Prog}
      {path : Prog.SourcePath} {source : Func}
      (cursor : Exec.Frame.SourceCursor frame program path source),
      cursor.node = current →
      some frame.sevm.code.toList = program.compile →
      ∀ (target : Exec.Deriv),
        Exec.Deriv.ParentPrefix cursor.node target →
        Ninst.At target.sevm.code target.pc (.reg .sstore) →
        ∃ site : Prog.SourceSite,
          site ∈ program.sourceSites ∧
          site.pc = target.pc ∧
          site.instruction = .reg .sstore
  apply Exec.Deriv.strongRec property
  intro current ih frame program path source cursor hcurrent compiled target reached storeAt
  subst current
  cases source with
  | last outcome =>
      have lastAt : Linst.At frame.sevm.code cursor.pc outcome :=
        Linst.at_of_slice cursor.codeSlice
      cases reached with
      | refl => exact (storeAt.false_of_linstAt lastAt).elim
      | step edge suffix =>
          exact (edge.false_of_linstAt lastAt).elim
  | next instruction tail =>
      cases reached with
      | refl =>
          let site : Prog.SourceSite :=
            { path := path, pc := cursor.pc, instruction := instruction }
          have localMember : site ∈
              Func.sourceSites path.functionIndex path.steps cursor.pc
                (.next instruction tail) := by
            rcases path with ⟨functionIndex, steps⟩
            simp [site, Func.sourceSites]
          have sourceAt : Ninst.At frame.sevm.code cursor.pc instruction :=
            Func.sourceSites_sound cursor.codeSlice cursor.codeBoundary
              localMember
          have instructionEq := Ninst.at_unique sourceAt storeAt
          cases instructionEq
          exact ⟨site, cursor.sourceIncluded localMember, rfl, rfl⟩
      | step occurrenceEdge suffix =>
          rcases cursor.next with ⟨tailCursor, sourceEdge⟩
          cases occurrenceEdge.unique sourceEdge
          exact ih tailCursor.node sourceEdge.lt tailCursor rfl compiled target
            suffix storeAt
  | branch left right =>
      rcases cursor.branch with
        ⟨arm, compilerPrefix, decrease⟩ |
        ⟨arm, compilerPrefix, decrease⟩
      · exact ih arm.node decrease arm rfl compiled target
          (compilerPrefix.trim reached storeAt) storeAt
      · exact ih arm.node decrease arm rfl compiled target
          (compilerPrefix.trim reached storeAt) storeAt
  | call index =>
      rcases cursor.call compiled with
        ⟨body, hbody, bodyCursor, compilerPrefix, decrease⟩
      exact ih bodyCursor.node decrease bodyCursor rfl compiled target
        (compilerPrefix.trim reached storeAt) storeAt

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
  exact Exec.Frame.SourceCursor.sstoreSite_core cursor.node cursor rfl
    compiled write.occurrence.node reached storeAt

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
  rcases Exec.Frame.SourceCursor.main invocation with
    ⟨mainCursor, compilerPrefix⟩
  have storeAt : Ninst.At write.occurrence.node.sevm.code
      write.occurrence.node.pc (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  have reached := compilerPrefix.trim sameFrame storeAt
  exact mainCursor.sstoreSite invocation.2.2.2 write reached

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
