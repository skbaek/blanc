import Blanc.ExecutionOccurrence

/-!
Cycle-safe certificates for same-frame source-level SSTORE-occurrence freedom.

The executable certificate scans each selected source body locally and treats
`Func.call` as an edge into a finite supplied component. It never recursively
traverses the source call graph, so self-loops and multi-node cycles can be
accepted. The execution theorem instead follows one actual finite
`Exec.Deriv.SourceCursor` and therefore requires neither source acyclicity nor
any success, commitment, or settlement premise.

This module says only that source `.reg .sstore` does not occur along the
selected same-frame execution prefix. It does not establish storage equality,
termination, gas sufficiency, settlement survival, child-frame freedom, or
absence of TSTORE, logs, balance, memory, code, creation, or selfdestruct
effects. It also says nothing about installation, authorization, transaction
behavior, ABI coverage, or any particular contract or Lido behavior until a
consumer supplies the exact compiled cursor and accepted certificate.
-/

namespace Blanc

open Jaune

/-! ## Executable certificate and exact logical reflection -/

/-- A source body contains no source-level `.reg .sstore` instruction.
Internal `Func.call` nodes are edges and are locally SSTORE-free. -/
def Func.LocalSstoreFree : Func → Prop
  | .last _ => True
  | .call _ => True
  | .branch left right =>
      left.LocalSstoreFree ∧ right.LocalSstoreFree
  | .next instruction tail =>
      instruction ≠ .reg .sstore ∧ tail.LocalSstoreFree

/-- Total structural checker for source-level SSTORE freedom in one body.
It inspects both branch arms and never follows an internal call edge. -/
def Func.localSstoreFree : Func → Bool
  | .last _ => true
  | .call _ => true
  | .branch left right =>
      left.localSstoreFree && right.localSstoreFree
  | .next (.reg .sstore) _ => false
  | .next _ tail => tail.localSstoreFree

/-- Exact reflection for the local structural checker. -/
theorem Func.localSstoreFree_iff {body : Func} :
    body.localSstoreFree = true ↔ body.LocalSstoreFree := by
  induction body with
  | last outcome =>
      simp [Func.localSstoreFree, Func.LocalSstoreFree]
  | call index =>
      simp [Func.localSstoreFree, Func.LocalSstoreFree]
  | branch left right left_ih right_ih =>
      simp [Func.localSstoreFree, Func.LocalSstoreFree, left_ih, right_ih]
  | next instruction tail tail_ih =>
      cases instruction with
      | reg operation =>
          cases operation <;>
            simp [Func.localSstoreFree, Func.LocalSstoreFree, tail_ih]
      | exec operation =>
          simp [Func.localSstoreFree, Func.LocalSstoreFree, tail_ih]
      | push bytes size =>
          simp [Func.localSstoreFree, Func.LocalSstoreFree, tail_ih]

private theorem Func.callsIn_mem_iff {body : Func} {members : List Nat} :
    body.callsIn (fun index => index ∈ members) = true ↔
      body.CallsIn (fun index => index ∈ members) := by
  induction body with
  | last outcome =>
      simp [Func.callsIn, Func.CallsIn]
  | call index =>
      simp [Func.callsIn, Func.CallsIn]
  | next instruction tail tail_ih =>
      simpa [Func.callsIn, Func.CallsIn] using tail_ih
  | branch left right left_ih right_ih =>
      simp [Func.callsIn, Func.CallsIn, left_ih, right_ih]

/-- Resolve the compiler function-table index used by `Func.call`.
Index zero is the program's main body and index one is its first auxiliary
body. -/
def Prog.function? (program : Prog) (index : Nat) : Option Func :=
  (program.main :: program.aux)[index]?

/-- Logical finite closed-component specification. Every selected index
resolves, its body is locally SSTORE-free, and every internal call stays in
the component. -/
def Prog.ClosedSstoreFree
    (program : Prog) (members : List Nat) : Prop :=
  ∀ index, index ∈ members →
    ∃ body, program.function? index = some body ∧
      body.LocalSstoreFree ∧
      body.CallsIn (fun callee => callee ∈ members)

/-- Total finite closed-component checker. It iterates the supplied list and
does not recursively traverse internal call edges, so source cycles can pass.
-/
def Prog.componentSstoreFree
    (program : Prog) (members : List Nat) : Bool :=
  members.all fun index =>
    match program.function? index with
    | none => false
    | some body =>
        body.localSstoreFree &&
          body.callsIn (fun callee => callee ∈ members)

/-- Exact reflection for the finite closed-component checker. -/
theorem Prog.componentSstoreFree_iff
    {program : Prog} {members : List Nat} :
    program.componentSstoreFree members = true ↔
      program.ClosedSstoreFree members := by
  constructor
  · intro accepted index member
    have selected :
        (match program.function? index with
          | none => false
          | some body =>
              body.localSstoreFree &&
                body.callsIn (fun callee => callee ∈ members)) = true :=
      (List.all_eq_true.mp accepted) index member
    cases lookup : program.function? index with
    | none =>
        simp [lookup] at selected
    | some body =>
        simp only [lookup, Bool.and_eq_true] at selected
        exact ⟨body, rfl,
          Func.localSstoreFree_iff.mp selected.1,
          Func.callsIn_mem_iff.mp selected.2⟩
  · intro specified
    apply List.all_eq_true.mpr
    intro index member
    rcases specified index member with
      ⟨body, lookup, localFree, callsClosed⟩
    simp only [lookup, Bool.and_eq_true]
    exact ⟨Func.localSstoreFree_iff.mpr localFree,
      Func.callsIn_mem_iff.mpr callsClosed⟩

/-- Logical entry/gateway applicability. The exact cursor body is locally
safe, all of its internal calls enter the selected component, and that
component is finite, lookup-total at selected indices, locally safe, and
closed. -/
def Prog.EntrySstoreFree
    (program : Prog) (entry : Func) (members : List Nat) : Prop :=
  entry.LocalSstoreFree ∧
    entry.CallsIn (fun callee => callee ∈ members) ∧
    program.ClosedSstoreFree members

/-- Executable entry-and-component certificate. -/
def Prog.entrySstoreFree
    (program : Prog) (entry : Func) (members : List Nat) : Bool :=
  entry.localSstoreFree &&
    entry.callsIn (fun callee => callee ∈ members) &&
    program.componentSstoreFree members

/-- Exact completeness and soundness of the executable entry-and-component
certificate against its logical specification. -/
theorem Prog.entrySstoreFree_iff
    {program : Prog} {entry : Func} {members : List Nat} :
    program.entrySstoreFree entry members = true ↔
      program.EntrySstoreFree entry members := by
  constructor
  · intro accepted
    simp only [Prog.entrySstoreFree, Bool.and_eq_true] at accepted
    exact ⟨Func.localSstoreFree_iff.mp accepted.1.1,
      Func.callsIn_mem_iff.mp accepted.1.2,
      Prog.componentSstoreFree_iff.mp accepted.2⟩
  · rintro ⟨localFree, callsClosed, component⟩
    simp only [Prog.entrySstoreFree, Bool.and_eq_true]
    exact ⟨⟨Func.localSstoreFree_iff.mpr localFree,
      Func.callsIn_mem_iff.mpr callsClosed⟩,
      Prog.componentSstoreFree_iff.mpr component⟩

/-- Named soundness direction for consumers of the executable certificate. -/
theorem Prog.entrySstoreFree_sound
    {program : Prog} {entry : Func} {members : List Nat}
    (accepted : program.entrySstoreFree entry members = true) :
    program.EntrySstoreFree entry members :=
  Prog.entrySstoreFree_iff.mp accepted

/-- The component-only finite scan accepts the empty component vacuously. -/
@[simp] theorem Prog.componentSstoreFree_nil (program : Prog) :
    program.componentSstoreFree [] = true := rfl

/-- An empty component certifies exactly a locally SSTORE-free, call-free
entry. -/
theorem Prog.entrySstoreFree_nil_iff
    {program : Prog} {entry : Func} :
    program.entrySstoreFree entry [] = true ↔
      entry.localSstoreFree = true ∧ entry.callFree = true := by
  simp [Prog.entrySstoreFree, Func.callFree]

/-- Duplicating an already selected index adds no certificate authority. -/
theorem Prog.entrySstoreFree_duplicate_iff
    {program : Prog} {entry : Func} {index : Nat} {members : List Nat} :
    program.entrySstoreFree entry (index :: index :: members) = true ↔
      program.entrySstoreFree entry (index :: members) = true := by
  simp only [Prog.entrySstoreFree_iff]
  simp [Prog.EntrySstoreFree, Prog.ClosedSstoreFree]

/-- Removing every duplicate from the finite member list preserves exactly the
same entry-and-component authority. -/
theorem Prog.entrySstoreFree_eraseDups_iff
    {program : Prog} {entry : Func} {members : List Nat} :
    program.entrySstoreFree entry members.eraseDups = true ↔
      program.entrySstoreFree entry members = true := by
  simp only [Prog.entrySstoreFree_iff]
  simp [Prog.EntrySstoreFree, Prog.ClosedSstoreFree]

/-! ## Arbitrary-outcome same-frame execution soundness -/

private theorem Exec.Deriv.SourceCursor.noSstore_core :
    ∀ current : Exec.Deriv,
      ∀ {root : Exec.Deriv} {program : Prog}
        {path : Prog.SourcePath} {source : Func}
        (cursor : Exec.Deriv.SourceCursor root program path source),
        cursor.node = current →
        some root.sevm.code.toList = program.compile →
        ∀ (members : List Nat),
          source.LocalSstoreFree →
          source.CallsIn (fun callee => callee ∈ members) →
          program.ClosedSstoreFree members →
          ∀ target : Exec.Deriv,
            Exec.Deriv.ParentPrefix cursor.node target →
            Ninst.At target.sevm.code target.pc (.reg .sstore) →
            False := by
  let property : Exec.Deriv.Pred := fun current =>
    ∀ {root : Exec.Deriv} {program : Prog}
      {path : Prog.SourcePath} {source : Func}
      (cursor : Exec.Deriv.SourceCursor root program path source),
      cursor.node = current →
      some root.sevm.code.toList = program.compile →
      ∀ (members : List Nat),
        source.LocalSstoreFree →
        source.CallsIn (fun callee => callee ∈ members) →
        program.ClosedSstoreFree members →
        ∀ target : Exec.Deriv,
          Exec.Deriv.ParentPrefix cursor.node target →
          Ninst.At target.sevm.code target.pc (.reg .sstore) →
          False
  apply Exec.Deriv.strongRec property
  intro current ih root program path source cursor hcurrent compiled members
    sourceFree sourceClosed component target reached storeAt
  subst current
  cases source with
  | last outcome =>
      have lastAt : Linst.At root.sevm.code cursor.pc outcome :=
        Linst.at_of_slice cursor.codeSlice
      cases reached with
      | refl =>
          exact storeAt.false_of_linstAt lastAt
      | step edge suffix =>
          exact edge.false_of_linstAt lastAt
  | next instruction tail =>
      change instruction ≠ .reg .sstore ∧
        tail.LocalSstoreFree at sourceFree
      change tail.CallsIn
        (fun callee => callee ∈ members) at sourceClosed
      cases reached with
      | refl =>
          let site : Prog.SourceSite :=
            { path := path
              pc := cursor.pc
              instruction := instruction }
          have localMember : site ∈
              Func.sourceSites path.functionIndex path.steps cursor.pc
                (.next instruction tail) := by
            rcases path with ⟨functionIndex, steps⟩
            simp [site, Func.sourceSites]
          have sourceAt :
              Ninst.At root.sevm.code cursor.pc instruction :=
            Func.sourceSites_sound cursor.codeSlice cursor.codeBoundary
              localMember
          exact sourceFree.1 (Ninst.at_unique sourceAt storeAt)
      | step occurrenceEdge suffix =>
          rcases cursor.nextOfParentStep occurrenceEdge with
            ⟨tailCursor, tailNodeEq⟩
          rw [← tailNodeEq] at suffix
          exact ih _ occurrenceEdge.lt tailCursor tailNodeEq compiled members
            sourceFree.2 sourceClosed component target suffix storeAt
  | branch left right =>
      change left.LocalSstoreFree ∧
        right.LocalSstoreFree at sourceFree
      change left.CallsIn (fun callee => callee ∈ members) ∧
        right.CallsIn (fun callee => callee ∈ members) at sourceClosed
      rcases cursor.branchToward reached storeAt with
        ⟨arm, compilerPrefix, armReached, decrease⟩ |
        ⟨arm, compilerPrefix, armReached, decrease⟩
      · exact ih arm.node decrease arm rfl compiled members
          sourceFree.1 sourceClosed.1 component target armReached storeAt
      · exact ih arm.node decrease arm rfl compiled members
          sourceFree.2 sourceClosed.2 component target armReached storeAt
  | call index =>
      change index ∈ members at sourceClosed
      rcases cursor.callToward compiled reached storeAt with
        ⟨body, hbody, bodyCursor, compilerPrefix, bodyReached, decrease⟩
      rcases component index sourceClosed with
        ⟨certBody, hcertBody, certFree, certClosed⟩
      have bodyEq : body = certBody :=
        Option.some.inj (hbody.symm.trans hcertBody)
      subst certBody
      exact ih bodyCursor.node decrease bodyCursor rfl compiled members
        certFree certClosed component target bodyReached storeAt

/-- Same-frame source-level SSTORE-occurrence freedom for an arbitrary-outcome
cursor. The proof follows the finite actual execution derivation; it makes no
success, commitment, settlement, termination, gas, or acyclicity assumption.
-/
theorem Exec.Deriv.SourceCursor.noSstore_of_entrySstoreFree
    {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (members : List Nat)
    (accepted : program.entrySstoreFree source members = true)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    False := by
  rcases Prog.entrySstoreFree_sound accepted with
    ⟨sourceFree, sourceClosed, component⟩
  exact Exec.Deriv.SourceCursor.noSstore_core cursor.node cursor rfl
    compiled members sourceFree sourceClosed component target reached storeAt

/-- An arbitrary-outcome instruction occurrence owned by an accepted
same-frame source cursor cannot be source-level SSTORE. Child-frame occurrences
require their own cursor and certificate. -/
theorem Exec.NinstOccurrence.instruction_ne_sstore_of_entrySstoreFree
    {root : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (members : List Nat)
    (accepted : program.entrySstoreFree source members = true)
    (occurrence : Exec.NinstOccurrence root)
    (owned : Exec.Deriv.ParentPrefix cursor.node occurrence.node) :
    occurrence.instruction ≠ .reg .sstore := by
  intro instructionEq
  have storeAt :
      Ninst.At occurrence.node.sevm.code occurrence.node.pc
        (.reg .sstore) := by
    simpa [instructionEq] using occurrence.decoded
  exact cursor.noSstore_of_entrySstoreFree compiled members accepted
    owned storeAt

/-- Raw exact-main specialization. Exact compiled invocation plus an accepted
main-entry/component certificate rules out every reached same-frame source
SSTORE on the supplied finite arbitrary-outcome prefix. -/
theorem Exec.Deriv.noSstore_of_exactMain_entrySstoreFree
    {root target : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (members : List Nat)
    (accepted : program.entrySstoreFree program.main members = true)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    False := by
  rcases Exec.Deriv.SourceCursor.mainToward invocation sameFrame storeAt with
    ⟨cursor, compilerPrefix, reached⟩
  exact cursor.noSstore_of_entrySstoreFree invocation.2.2.2 members
    accepted reached storeAt

end Blanc
