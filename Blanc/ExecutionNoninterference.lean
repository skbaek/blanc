import Blanc.ExecutionOccurrence

/-!
# Contract-neutral retained-write noninterference

This module builds exact persistent-cell noninterference over the frozen
execution-occurrence substrate.  It is separate from that predecessor because
the occurrence and transient-settlement assurance gates pin the predecessor's
surface and implementation byte-for-byte.
-/

namespace Blanc

open Jaune

/-- No settlement-retained successful SSTORE in the selected invocation's
frame closure targets one exact persistent-storage cell.  The owner projection
keeps this semantic under ordinary CALL, proxy, and callback compositions. -/
def Exec.NoRetainedWriteTo
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (owner : Adr) (key : B256) : Prop :=
  ∀ write ∈ Exec.retainedStorageWrites run,
    write.matches owner key ≠ true

/-- A noncommitting invocation retains no storage write at all, hence cannot
retain a write to any selected persistent cell.  This is the rollback-first
route to `NoRetainedWriteTo`; committing executions use the childless or
frame-owner routes below. -/
theorem Exec.noRetainedWriteTo_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (notCommitted : Execution.commits out ≠ true)
    (owner : Adr) (key : B256) :
    Exec.NoRetainedWriteTo run owner key := by
  intro write member
  have nodes := Exec.retainedNodes_eq_nil_of_not_commits run notCommitted
  exact False.elim (by
    simp [Exec.retainedStorageWrites, nodes] at member)

private theorem Exec.StorageWrite.foldlCell_eq_of_noRetainedWriteTo
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
      simp only [if_neg (none head (by simp))]
      apply ih initial
      intro write member
      exact none write (by
        simp [member])

/-- Absence of a retained successful write to one cell preserves that cell in
every committing outcome of the invocation frame closure. -/
theorem Exec.committedCell_eq_of_noRetainedWriteTo
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (owner : Adr) (key : B256)
    (noWrite : Exec.NoRetainedWriteTo run owner key) :
    (Devm.getStor (Execution.committedPost out committed) owner).get key =
      (Devm.getStor pre owner).get key := by
  rw [Exec.storageReplay_committedPost run committed owner key]
  exact Exec.StorageWrite.foldlCell_eq_of_noRetainedWriteTo _ noWrite

/-- Same-frame continuation never changes the static execution environment. -/
theorem Exec.Deriv.ParentStep.sevm_eq
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) : next.sevm = root.sevm := by
  cases edge <;> rfl

/-- Every endpoint of a same-frame prefix has the root's static environment. -/
theorem Exec.Deriv.ParentPrefix.sevm_eq
    {root tail : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root tail) : tail.sevm = root.sevm := by
  induction chain with
  | refl => rfl
  | step head rest ih => exact ih.trans head.sevm_eq

/-- A direct invocation that enters no child frame cannot write somebody
else's storage.  This is a sufficient route to the semantic predicate above,
not its converse: an invocation may enter benign children and still satisfy
`NoRetainedWriteTo`. -/
theorem Exec.noRetainedWriteTo_of_no_execOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (owner : Adr) (key : B256)
    (differentOwner : sevm.currentTarget ≠ owner)
    (childless : ∀ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      ∀ x : Xinst, occurrence.instruction ≠ .exec x) :
    Exec.NoRetainedWriteTo run owner key := by
  intro event member hmatch
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
      (event := event) member with ⟨write, -, writeEq⟩
  subst event
  have noDescendants :=
    Exec.rawFrameDescendants_eq_nil_of_no_execOccurrence run childless
  have sameFrame :=
    Exec.Deriv.parentPrefix_of_mem_rawNodes_of_rawFrameDescendants_eq_nil
      noDescendants write.occurrence.reached
  have ownerEq := (Exec.StorageWrite.matches_eq_true.mp hmatch).1
  change write.occurrence.node.sevm.currentTarget = owner at ownerEq
  rw [sameFrame.sevm_eq] at ownerEq
  exact differentOwner ownerEq

/-- If every actually entered code frame owns storage at an address different
from the selected owner, then no retained write in the complete invocation
tree can target that owner's cell.  Unlike the childless sufficient route,
this theorem directly admits ordinary CALL trees whose callees have distinct
storage owners. -/
theorem Exec.noRetainedWriteTo_of_frame_owners_ne
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (owner : Adr) (key : B256)
    (different : ∀ frameRoot ∈ Exec.rawFrameRoots run,
      frameRoot.sevm.currentTarget ≠ owner) :
    Exec.NoRetainedWriteTo run owner key := by
  intro event member matchEq
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
      (event := event) member with ⟨write, -, writeEq⟩
  subst event
  rcases (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run
      write.occurrence.node).mp write.occurrence.reached with
    ⟨frameRoot, frameMember, sameFrame⟩
  have ownerEq := (Exec.StorageWrite.matches_eq_true.mp matchEq).1
  change write.occurrence.node.sevm.currentTarget = owner at ownerEq
  rw [sameFrame.sevm_eq] at ownerEq
  exact different frameRoot frameMember ownerEq

/-- A source-level absence of executable instructions is a named sufficient
route from exact compiled invocation identity to semantic storage
noninterference.  This theorem is intentionally one-way: source programs with
benign calls can establish `NoRetainedWriteTo` by other means. -/
theorem Exec.noRetainedWriteTo_of_sourceSites_no_exec
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) {program : Prog}
    {storageTarget codeAddress owner : Adr} (key : B256)
    (invocation :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        program storageTarget codeAddress)
    (differentOwner : storageTarget ≠ owner)
    (sourceNoExec : ∀ site ∈ program.sourceSites, ∀ x : Xinst,
      site.instruction ≠ .exec x) :
    Exec.NoRetainedWriteTo run owner key := by
  let root : Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  have noSameFrame : ∀ node : Exec.Deriv,
      Exec.Deriv.ParentPrefix root node →
      ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x) := by
    intro node sameFrame x instructionAt
    rcases root.nonPush_sourceSite invocation sameFrame (by trivial)
        instructionAt with ⟨site, member, -, instructionEq⟩
    exact sourceNoExec site member x instructionEq
  have noDescendants : Exec.rawFrameDescendants run = [] :=
    Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt run noSameFrame
  have childless : ∀ occurrence : Exec.NinstOccurrence root,
      ∀ x : Xinst, occurrence.instruction ≠ .exec x := by
    intro occurrence x instructionEq
    have sameFrame :=
      Exec.Deriv.parentPrefix_of_mem_rawNodes_of_rawFrameDescendants_eq_nil
        noDescendants occurrence.reached
    have nonPush : NinstNonPush occurrence.instruction := by
      rw [instructionEq]
      trivial
    rcases root.nonPush_sourceSite invocation sameFrame nonPush
        occurrence.decoded with ⟨site, member, -, sourceEq⟩
    exact sourceNoExec site member x (sourceEq.trans instructionEq)
  apply Exec.noRetainedWriteTo_of_no_execOccurrence run owner key
  · rw [invocation.2.1]
    exact differentOwner
  · exact childless

end Blanc
