import Blanc.ExecutionNoninterference
import Blanc.ExecutionCellProvenance
import Blanc.Lift.TargetLogEvents

/-!
# Persistent cells at actual settlement-retained node entries

At each retained entry, the cell comes from its initial value or a strictly
earlier retained write. Absence of retained writes then gives equality. Raw
nodes of rolled-back children are deliberately outside the conclusion.
-/

namespace Blanc

open Jaune

/-- At an actual retained node entry, the observed cell is its root entry
value or a successful write at a strictly earlier retained node. Complete
child settlement governs the prefix; no absence-of-writes premise is used. -/
theorem Exec.retainedNodes_cellProv_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (key : B256) (hsg : sevm.benvStat.rules.stateGas = none)
    {owner : Adr} (hcode : (pre.getCode owner).toList ≠ [])
    {before : List Exec.Deriv} {node : Exec.Deriv} {after : List Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ node :: after) :
    CellProv owner key ((pre.getStor owner).get key) before
      ((node.devm.getStor owner).get key) := by
  induction run generalizing before node after with
  | halt step =>
      simp only [Exec.retainedNodes_eq_of_commits _ committed,
        Exec.retainedNodesOfCommits] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨_, impossible⟩ := split
          have length := congrArg List.length impossible
          simp only [List.length_nil, List.length_append, List.length_cons] at length
          omega
  | @cont pc sevm pre pc' post out step next ih =>
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons r rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, nextSplit⟩ := split
          have code := Exec.Deriv.ParentStep.codePreserve (.cont step next) owner hcode
          have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
          have hopSplit : Exec.rawNodes (.cont step next) =
              [⟨pc, sevm, pre, out, .cont step next⟩] ++
                ⟨pc', sevm, post, out, next⟩ :: (Exec.rawNodes next).tail := by
            cases next <;> simp only [Exec.rawNodes, List.tail_cons,
              List.cons_append, List.nil_append]
          have hop := Exec.rawNodes_cellProv_noStateGas (.cont step next) key hsg
            rfl hcode hopSplit
          exact hop.trans (ih committed hsg nextCode nextSplit)
  | doneErr step enter resume =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre frame resume pc' settled post out step enter resumed next ih =>
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact Or.inl rfl
      | cons r rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, nextSplit⟩ := split
          have code := Exec.Deriv.ParentStep.codePreserve
            (.doneOk step enter resumed next) owner hcode
          have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
          have tail := ih committed hsg nextCode nextSplit
          rw [Evm.step_doneOk_getStor_eq step enter resumed owner
            (State.Protected.of_code_ne_nil hcode)] at tail
          exact tail.mono_right [⟨pc, sevm, pre, out, .doneOk step enter resumed next⟩]
  | runErr step enter child resume ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child
      resumed next childIH nextIH =>
      have code := Exec.Deriv.ParentStep.codePreserve
        (.runOk step enter child resumed next) owner hcode
      have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
      have childCode : (childEvm.dyna.getCode owner).toList ≠ [] := by
        rw [(Evm.step_spawn_child step enter).2.1 owner]
        exact hcode
      have childSg := Evm.step_spawn_child_fork_noStateGas step enter hsg
      have entryCell := congrArg (Stor.get · key)
        (Evm.step_spawn_enter_getStor_noStateGas hsg step enter hcode)
      obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
      have nonempty : pre.getCode owner ≠ .empty := by
        intro empty
        apply hcode
        rw [empty]
        exact ByteArray.toList_empty
      have seam := Xinst.spawn_run_getStor_noStateGas hsg spawn enter child resumed nonempty
      by_cases settles : frame.settlementCommits raw = true
      · rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles]
          at split
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            obtain ⟨rfl, rfl⟩ := split
            exact Or.inl rfl
        | cons r rest =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, remaining⟩ := split
            have childCommitted := Frame.raw_commits_of_settlementCommits settles
            rcases List.split_append_cons remaining with
              ⟨suffix, childSplit, _⟩ | ⟨earlier, restEq, nextSplit⟩
            · have atChild := childIH childCommitted childSg childCode childSplit
              rw [entryCell] at atChild
              exact atChild.mono_right
                [⟨pc, sevm, pre, out, .runOk step enter child resumed next⟩]
            · rw [restEq]
              have childReplay := (Exec.storageReplay_committedPost_noStateGas
                child childCommitted childSg).2 owner childCode key
              have postProv : CellProv owner key ((pre.getStor owner).get key)
                  (Exec.retainedNodes child) ((post.getStor owner).get key) := by
                apply CellProv.of_replayCell
                · rw [seam.1 settles key, ← entryCell]
                  exact childReplay.symm
                · intro write present
                  exact List.mem_filterMap.mp present
              exact (postProv.mono_right
                [⟨pc, sevm, pre, out, .runOk step enter child resumed next⟩]).trans
                (nextIH committed hsg nextCode nextSplit)
      · rw [Exec.retainedNodes_runOk_of_not_settlementCommits _ _ _ _ _ committed settles]
          at split
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            obtain ⟨rfl, rfl⟩ := split
            exact Or.inl rfl
        | cons r rest =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, nextSplit⟩ := split
            have tail := nextIH committed hsg nextCode nextSplit
            rw [seam.2 settles key] at tail
            exact tail.mono_right
              [⟨pc, sevm, pre, out, .runOk step enter child resumed next⟩]

/-- A committing invocation with no retained write to the observed cell keeps
that cell at every actual retained node entry. This is the equality projection
of strict retained-prefix provenance; reverted raw writes remain allowed. -/
theorem Exec.retainedNode_cell_eq_of_noRetainedWriteTo_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) (owner : Adr) (key : B256)
    (hcode : (pre.getCode owner).toList ≠ [])
    (noWrite : Exec.NoRetainedWriteTo run owner key)
    {node : Exec.Deriv} (retained : node ∈ Exec.retainedNodes run) :
    (node.devm.getStor owner).get key = (pre.getStor owner).get key := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp retained
  have prov := Exec.retainedNodes_cellProv_noStateGas run committed key hsg hcode split
  rcases prov with equal | ⟨b₁, b₂, m, write, earlierSplit, found, own, hit, _⟩
  · exact equal
  · have earlier : m ∈ before := by
      rw [earlierSplit]
      exact List.mem_append_right _ List.mem_cons_self
    have all : m ∈ Exec.retainedNodes run := by
      rw [split]
      exact List.mem_append_left _ earlier
    exact (noWrite write (List.mem_filterMap.mpr ⟨m, all, found⟩)
      (Exec.StorageWrite.matches_eq_true.mpr ⟨own, hit⟩)).elim

end Blanc
