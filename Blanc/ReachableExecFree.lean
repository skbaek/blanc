import Blanc.CycleWriteFree
import Blanc.ExecutionNoninterference
import Blanc.LinearDispatch

/-!
# Cycle-safe reachable source exec freedom

This module certifies that one selected source entry and a finite,
call-closed component contain no source-level `.exec` instruction. Internal
`Func.call` nodes are edges rather than forbidden instructions, so recursive
and mutually recursive source components are accepted without recursively
evaluating the call graph. Both branch arms inside every selected body are
checked.

The certificate is deliberately local to the supplied entry and component.
It does not claim that the whole `Prog` is exec-free, that compiler glue is
source code, that an execution terminates or commits, that external children
have any outcome, or that storage, memory, balances, logs, gas, settlement,
authorization, installation, ABI coverage, or any contract-specific property
is preserved. Those consequences require separate execution and semantic
bridges.
-/

namespace Blanc

open Jaune

/-! ## Executable certificate and exact logical reflection -/

/-- A source body contains no source-level `.exec` instruction. Internal
`Func.call` nodes are edges and are locally exec-free. -/
def Func.LocalExecFree : Func → Prop
  | .last _ => True
  | .call _ => True
  | .branch left right =>
      left.LocalExecFree ∧ right.LocalExecFree
  | .next instruction tail =>
      (∀ x : Xinst, instruction ≠ .exec x) ∧ tail.LocalExecFree

/-- Total structural checker for source-level exec freedom in one body. It
inspects both branch arms and never follows an internal call edge. -/
def Func.localExecFree : Func → Bool
  | .last _ => true
  | .call _ => true
  | .branch left right =>
      left.localExecFree && right.localExecFree
  | .next (.exec _) _ => false
  | .next _ tail => tail.localExecFree

/-- Exact reflection for the local structural checker. -/
theorem Func.localExecFree_iff {body : Func} :
    body.localExecFree = true ↔ body.LocalExecFree := by
  induction body with
  | last outcome =>
      simp [Func.localExecFree, Func.LocalExecFree]
  | call index =>
      simp [Func.localExecFree, Func.LocalExecFree]
  | branch left right left_ih right_ih =>
      simp [Func.localExecFree, Func.LocalExecFree, left_ih, right_ih]
  | next instruction tail tail_ih =>
      cases instruction with
      | reg operation =>
          simp [Func.localExecFree, Func.LocalExecFree, tail_ih]
      | exec operation =>
          simp [Func.localExecFree, Func.LocalExecFree]
      | push bytes size =>
          simp [Func.localExecFree, Func.LocalExecFree, tail_ih]

/-- Logical finite closed-component specification. Every selected index
resolves through the compiler function table, its body is locally exec-free,
and every internal call stays in the selected component. -/
def Prog.ClosedExecFree
    (program : Prog) (members : List Nat) : Prop :=
  ∀ index, index ∈ members →
    ∃ body, program.function? index = some body ∧
      body.LocalExecFree ∧
      body.CallsIn (fun callee => callee ∈ members)

/-- Total finite closed-component checker. It scans the supplied list and
does not recursively follow internal call edges, so source cycles terminate. -/
def Prog.componentExecFree
    (program : Prog) (members : List Nat) : Bool :=
  members.all fun index =>
    match program.function? index with
    | none => false
    | some body =>
        body.localExecFree &&
          body.callsIn (fun callee => callee ∈ members)

/-- Exact reflection for the finite closed-component checker. -/
theorem Prog.componentExecFree_iff
    {program : Prog} {members : List Nat} :
    program.componentExecFree members = true ↔
      program.ClosedExecFree members := by
  constructor
  · intro accepted index member
    have selected :
        (match program.function? index with
          | none => false
          | some body =>
              body.localExecFree &&
                body.callsIn (fun callee => callee ∈ members)) = true :=
      (List.all_eq_true.mp accepted) index member
    cases lookup : program.function? index with
    | none =>
        simp [lookup] at selected
    | some body =>
        simp only [lookup, Bool.and_eq_true] at selected
        exact ⟨body, rfl,
          Func.localExecFree_iff.mp selected.1,
          Func.callsIn_mem_iff.mp selected.2⟩
  · intro specified
    apply List.all_eq_true.mpr
    intro index member
    rcases specified index member with
      ⟨body, lookup, localFree, callsClosed⟩
    simp only [lookup, Bool.and_eq_true]
    exact ⟨Func.localExecFree_iff.mpr localFree,
      Func.callsIn_mem_iff.mpr callsClosed⟩

/-- Route-entry applicability for a finite source call component.

The selected `entry` is checked structurally, including both arms of each
source branch. Every internal call from the entry must enter `members`; every
member must resolve through `Prog.function?`, be locally exec-free, and call
only another member. The finite list makes the certificate executable and
cycle-safe, but may conservatively include bodies the actual route never
visits.

This predicate speaks only about source `.exec` reachability through the
selected entry's internal-call closure. It does not constrain unselected
program bodies, compiler glue, dynamic child outcomes, commitment, settlement,
termination, gas, state effects, ownership, or any contract protocol. -/
def Prog.ReachableExecFree
    (program : Prog) (entry : Func) (members : List Nat) : Prop :=
  entry.LocalExecFree ∧
    entry.CallsIn (fun callee => callee ∈ members) ∧
    program.ClosedExecFree members

/-- Executable selected-entry and finite-component certificate. -/
def Prog.reachableExecFree
    (program : Prog) (entry : Func) (members : List Nat) : Bool :=
  entry.localExecFree &&
    entry.callsIn (fun callee => callee ∈ members) &&
    program.componentExecFree members

/-- Exact completeness and soundness of the executable certificate against
`Prog.ReachableExecFree`. -/
theorem Prog.reachableExecFree_iff
    {program : Prog} {entry : Func} {members : List Nat} :
    program.reachableExecFree entry members = true ↔
      program.ReachableExecFree entry members := by
  constructor
  · intro accepted
    simp only [Prog.reachableExecFree, Bool.and_eq_true] at accepted
    exact ⟨Func.localExecFree_iff.mp accepted.1.1,
      Func.callsIn_mem_iff.mp accepted.1.2,
      Prog.componentExecFree_iff.mp accepted.2⟩
  · rintro ⟨localFree, callsClosed, component⟩
    simp only [Prog.reachableExecFree, Bool.and_eq_true]
    exact ⟨⟨Func.localExecFree_iff.mpr localFree,
      Func.callsIn_mem_iff.mpr callsClosed⟩,
      Prog.componentExecFree_iff.mpr component⟩

/-- Named soundness direction for consumers of the executable certificate. -/
theorem Prog.reachableExecFree_sound
    {program : Prog} {entry : Func} {members : List Nat}
    (accepted : program.reachableExecFree entry members = true) :
    program.ReachableExecFree entry members :=
  Prog.reachableExecFree_iff.mp accepted

/-! ## Target-directed selector routing -/

/-- An actual target-directed route through a selector-unique linear
dispatcher reaches the body paired with the selector present at dispatcher
entry. The target is a source `.exec`, so compiler PUSH/JUMP glue cannot be
mistaken for the target. The theorem follows the retained arbitrary-outcome
`Exec` derivation and does not assume success, commitment, pc-freedom, or
termination. -/
theorem Exec.Deriv.SourceCursor.Toward.linearDispatchWith_selectedBody
    {root target : Exec.Deriv} {program : Prog}
    {initialPath : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource}
    {fallback : Nat} {selector : B256} {body : Func} {x : Xinst}
    (compiled : some root.sevm.code.toList = program.compile)
    (execAt : Ninst.At target.sevm.code target.pc (.exec x)) :
    ∀ (entries : List (B256 × Func)),
      selectorUnique entries →
      (selector, body) ∈ entries →
      ∀ {path : Prog.SourcePath} {stack : Stack}
        (cursor : Exec.Deriv.SourceCursor root program path
          (linearDispatchWith fallback entries)),
        Exec.Deriv.SourceCursor.Toward
            initial target (.exec x) cursor →
          selector :: stack <<+ cursor.pre.stack →
            ∃ bodyPath,
              ∃ bodyCursor : Exec.Deriv.SourceCursor root program
                  bodyPath body,
                Exec.Deriv.SourceCursor.Toward
                    initial target (.exec x) bodyCursor ∧
                  stack <<+ bodyCursor.pre.stack := by
  intro entries
  induction entries with
  | nil =>
      intro unique member
      simp at member
  | cons head tail ih =>
      rcases head with ⟨word, candidate⟩
      intro unique member path stack cursor route selectorPrefix
      cases tail with
      | nil =>
          have selected : (selector, body) = (word, candidate) :=
            List.mem_singleton.mp member
          cases selected
          change Exec.Deriv.SourceCursor root program path
            ([Ninst.pushB256 selector, Ninst.eq] +++
              (body <?> .call fallback)) at cursor
          rcases route.dropLineRun (by
              simp [Ninst.pushB256]) with
            ⟨branchPath, branchCursor, lineRun, branchChronology,
              branchRoute⟩
          rcases Line.of_run_cons lineRun with
            ⟨afterPush, pushRun, restRun⟩
          rcases Line.of_run_cons restRun with
            ⟨afterEq, eqRun, nilRun⟩
          cases nilRun
          have pushed : selector :: selector :: stack <<+ afterPush.stack := by
            simpa using prefix_of_push
              (of_run_pushB256 pushRun) selectorPrefix
          have flagPrefix :
              (selector =? selector) :: stack <<+ branchCursor.pre.stack :=
            prefix_of_eq eqRun pushed
          rw [show (selector =? selector) = 1 from by
            simp [B256.eqCheck]] at flagPrefix
          rcases branchRoute.selectBranchSucc branchCursor compiled
              (by trivial) execAt (by decide) flagPrefix with
            ⟨bodyCursor, bodyRoute, bodyPrefix⟩
          exact ⟨_, bodyCursor, bodyRoute, bodyPrefix⟩
      | cons next rest =>
          have pairwise :
              ((word, candidate) :: next :: rest).Pairwise
                (fun a b : B256 × Func => a.1 ≠ b.1) := by
            simpa [selectorUnique] using unique
          have tailUnique : selectorUnique (next :: rest) := by
            simpa [selectorUnique] using
              (List.pairwise_cons.mp pairwise).2
          rcases List.mem_cons.mp member with selected | tailMember
          · cases selected
            change Exec.Deriv.SourceCursor root program path
              ([Ninst.dup 0, Ninst.pushB256 selector, Ninst.eq] +++
                ((Ninst.pop ::: body) <?>
                  linearDispatchWith fallback (next :: rest))) at cursor
            rcases route.dropLineRun (by
                simp [Ninst.pushB256]) with
              ⟨branchPath, branchCursor, lineRun, branchChronology,
                branchRoute⟩
            rcases Line.of_run_cons lineRun with
              ⟨afterDup, dupRun, restRun⟩
            rcases Line.of_run_cons restRun with
              ⟨afterPush, pushRun, restRun⟩
            rcases Line.of_run_cons restRun with
              ⟨afterEq, eqRun, nilRun⟩
            cases nilRun
            have duplicated :
                selector :: selector :: stack <<+ afterDup.stack :=
              prefix_of_dup_val dupRun (by show_nth) selectorPrefix
            have pushed : selector :: selector :: selector :: stack <<+
                afterPush.stack := by
              simpa using prefix_of_push
                (of_run_pushB256 pushRun) duplicated
            have flagPrefix : (selector =? selector) :: selector :: stack <<+
                branchCursor.pre.stack :=
              prefix_of_eq eqRun pushed
            rw [show (selector =? selector) = 1 from by
              simp [B256.eqCheck]] at flagPrefix
            rcases branchRoute.selectBranchSucc branchCursor compiled
                (by trivial) execAt (by decide) flagPrefix with
              ⟨selectedCursor, selectedRoute, selectedPrefix⟩
            rcases selectedRoute.next_of_instruction_ne (by
                intro instructionEq
                cases instructionEq) with
              ⟨popChronology, bodyCursor, popEdge, bodyRoute⟩
            have popRun := selectedCursor.ninstRun_of_nextEdge popEdge
            have bodyPrefix : stack <<+ bodyCursor.pre.stack :=
              prefix_of_pop (of_run_pop popRun) selectedPrefix
            exact ⟨_, bodyCursor, bodyRoute, bodyPrefix⟩
          · have wordNe : word ≠ selector := by
              exact (List.pairwise_cons.mp pairwise).1
                (selector, body) tailMember
            change Exec.Deriv.SourceCursor root program path
              ([Ninst.dup 0, Ninst.pushB256 word, Ninst.eq] +++
                ((Ninst.pop ::: candidate) <?>
                  linearDispatchWith fallback (next :: rest))) at cursor
            rcases route.dropLineRun (by
                simp [Ninst.pushB256]) with
              ⟨branchPath, branchCursor, lineRun, branchChronology,
                branchRoute⟩
            rcases Line.of_run_cons lineRun with
              ⟨afterDup, dupRun, restRun⟩
            rcases Line.of_run_cons restRun with
              ⟨afterPush, pushRun, restRun⟩
            rcases Line.of_run_cons restRun with
              ⟨afterEq, eqRun, nilRun⟩
            cases nilRun
            have duplicated :
                selector :: selector :: stack <<+ afterDup.stack :=
              prefix_of_dup_val dupRun (by show_nth) selectorPrefix
            have pushed : word :: selector :: selector :: stack <<+
                afterPush.stack := by
              simpa using prefix_of_push
                (of_run_pushB256 pushRun) duplicated
            have flagPrefix : (word =? selector) :: selector :: stack <<+
                branchCursor.pre.stack :=
              prefix_of_eq eqRun pushed
            rw [show (word =? selector) = 0 from by
              simp [B256.eqCheck, wordNe]] at flagPrefix
            rcases branchRoute.selectBranchZero branchCursor compiled
                (by trivial) execAt flagPrefix with
              ⟨tailCursor, tailRoute, tailPrefix⟩
            exact ih tailUnique tailMember tailCursor tailRoute tailPrefix

/-! ## Arbitrary-outcome actual-execution soundness -/

private theorem Exec.Deriv.SourceCursor.noExec_core :
    ∀ current : Exec.Deriv,
      ∀ {root : Exec.Deriv} {program : Prog}
        {path : Prog.SourcePath} {source : Func}
        (cursor : Exec.Deriv.SourceCursor root program path source),
        cursor.node = current →
        some root.sevm.code.toList = program.compile →
        ∀ (members : List Nat),
          source.LocalExecFree →
          source.CallsIn (fun callee => callee ∈ members) →
          program.ClosedExecFree members →
          ∀ target : Exec.Deriv,
            Exec.Deriv.ParentPrefix cursor.node target →
            ∀ x : Xinst,
              Ninst.At target.sevm.code target.pc (.exec x) →
              False := by
  let property : Exec.Deriv.Pred := fun current =>
    ∀ {root : Exec.Deriv} {program : Prog}
      {path : Prog.SourcePath} {source : Func}
      (cursor : Exec.Deriv.SourceCursor root program path source),
      cursor.node = current →
      some root.sevm.code.toList = program.compile →
      ∀ (members : List Nat),
        source.LocalExecFree →
        source.CallsIn (fun callee => callee ∈ members) →
        program.ClosedExecFree members →
        ∀ target : Exec.Deriv,
          Exec.Deriv.ParentPrefix cursor.node target →
          ∀ x : Xinst,
            Ninst.At target.sevm.code target.pc (.exec x) →
            False
  apply Exec.Deriv.strongRec property
  intro current ih root program path source cursor hcurrent compiled members
    sourceFree sourceClosed component target reached x execAt
  subst current
  cases source with
  | last outcome =>
      have lastAt : Linst.At root.sevm.code cursor.pc outcome :=
        Linst.at_of_slice cursor.codeSlice
      cases reached with
      | refl =>
          exact execAt.false_of_linstAt lastAt
      | step edge suffix =>
          exact edge.false_of_linstAt lastAt
  | next instruction tail =>
      change (∀ x : Xinst, instruction ≠ .exec x) ∧
        tail.LocalExecFree at sourceFree
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
          exact sourceFree.1 x (Ninst.at_unique sourceAt execAt)
      | step occurrenceEdge suffix =>
          rcases cursor.nextOfParentStep occurrenceEdge with
            ⟨tailCursor, tailNodeEq⟩
          rw [← tailNodeEq] at suffix
          exact ih _ occurrenceEdge.lt tailCursor tailNodeEq compiled members
            sourceFree.2 sourceClosed component target suffix x execAt
  | branch left right =>
      change left.LocalExecFree ∧
        right.LocalExecFree at sourceFree
      change left.CallsIn (fun callee => callee ∈ members) ∧
        right.CallsIn (fun callee => callee ∈ members) at sourceClosed
      rcases cursor.branchToward reached (by trivial) execAt with
        ⟨arm, compilerPrefix, armReached, decrease⟩ |
        ⟨arm, compilerPrefix, armReached, decrease⟩
      · exact ih arm.node decrease arm rfl compiled members
          sourceFree.1 sourceClosed.1 component target armReached x execAt
      · exact ih arm.node decrease arm rfl compiled members
          sourceFree.2 sourceClosed.2 component target armReached x execAt
  | call index =>
      change index ∈ members at sourceClosed
      rcases cursor.callToward compiled reached (by trivial) execAt with
        ⟨body, hbody, bodyCursor, compilerPrefix, bodyReached, decrease⟩
      rcases component index sourceClosed with
        ⟨certBody, hcertBody, certFree, certClosed⟩
      have bodyEq : body = certBody :=
        Option.some.inj (hbody.symm.trans hcertBody)
      subst certBody
      exact ih bodyCursor.node decrease bodyCursor rfl compiled members
        certFree certClosed component target bodyReached x execAt

/-- Same-frame source-level exec-occurrence freedom for an arbitrary-outcome
actual execution cursor. The proof follows the finite `Exec.Deriv` selected by
the cursor; it assumes neither source acyclicity nor success, commitment,
settlement, termination, or gas sufficiency. -/
theorem Exec.Deriv.SourceCursor.noExec_of_reachableExecFree
    {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (members : List Nat)
    (accepted : program.reachableExecFree source members = true)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (x : Xinst)
    (execAt : Ninst.At target.sevm.code target.pc (.exec x)) :
    False := by
  rcases Prog.reachableExecFree_sound accepted with
    ⟨sourceFree, sourceClosed, component⟩
  exact Exec.Deriv.SourceCursor.noExec_core cursor.node cursor rfl
    compiled members sourceFree sourceClosed component target reached x execAt

/-- An instruction occurrence owned by an accepted same-frame source cursor
cannot be a source-level `.exec`. Child-frame occurrences require their own
cursor and certificate. -/
theorem Exec.NinstOccurrence.instruction_ne_exec_of_reachableExecFree
    {root : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (members : List Nat)
    (accepted : program.reachableExecFree source members = true)
    (occurrence : Exec.NinstOccurrence root)
    (owned : Exec.Deriv.ParentPrefix cursor.node occurrence.node)
    (x : Xinst) :
    occurrence.instruction ≠ .exec x := by
  intro instructionEq
  have execAt :
      Ninst.At occurrence.node.sevm.code occurrence.node.pc (.exec x) := by
    simpa [instructionEq] using occurrence.decoded
  exact cursor.noExec_of_reachableExecFree compiled members accepted
    owned x execAt

/-- Raw exact-main specialization. Exact compiled invocation plus an accepted
main-entry/component certificate rules out every reached same-frame source
`.exec` on the supplied finite arbitrary-outcome prefix. -/
theorem Exec.Deriv.noExec_of_exactMain_reachableExecFree
    {root target : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (members : List Nat)
    (accepted : program.reachableExecFree program.main members = true)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (x : Xinst)
    (execAt : Ninst.At target.sevm.code target.pc (.exec x)) :
    False := by
  rcases Exec.Deriv.SourceCursor.mainToward invocation sameFrame execAt with
    ⟨cursor, compilerPrefix, reached⟩
  exact cursor.noExec_of_reachableExecFree invocation.2.2.2 members
    accepted reached x execAt

/-- A same-frame `.exec` exclusion eliminates child frames and therefore
lifts to occurrence-level exec freedom for the complete raw invocation. -/
theorem Exec.noExecOccurrence_of_no_sameFrame_execAt
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (noSameFrame : ∀ target : Exec.Deriv,
      Exec.Deriv.ParentPrefix
          (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) target →
        ∀ x : Xinst,
          ¬ Ninst.At target.sevm.code target.pc (.exec x)) :
    ∀ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      ∀ x : Xinst, occurrence.instruction ≠ .exec x := by
  have noDescendants : Exec.rawFrameDescendants run = [] :=
    Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt run noSameFrame
  intro occurrence x instructionEq
  have sameFrame :=
    Exec.Deriv.parentPrefix_of_mem_rawNodes_of_rawFrameDescendants_eq_nil
      noDescendants occurrence.reached
  have execAt :
      Ninst.At occurrence.node.sevm.code occurrence.node.pc (.exec x) := by
    simpa [instructionEq] using occurrence.decoded
  exact noSameFrame occurrence.node sameFrame x execAt

/-- Same-frame `.exec` exclusion is a contract-neutral sufficient condition
for retained-write noninterference against a distinct storage owner. -/
theorem Exec.noRetainedWriteTo_of_no_sameFrame_execAt
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (owner : Adr) (key : B256)
    (differentOwner : sevm.currentTarget ≠ owner)
    (noSameFrame : ∀ target : Exec.Deriv,
      Exec.Deriv.ParentPrefix
          (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) target →
        ∀ x : Xinst,
          ¬ Ninst.At target.sevm.code target.pc (.exec x)) :
    Exec.NoRetainedWriteTo run owner key := by
  apply Exec.noRetainedWriteTo_of_no_execOccurrence run owner key
  · exact differentOwner
  · exact Exec.noExecOccurrence_of_no_sameFrame_execAt run noSameFrame

/-- Exact-main reachable exec freedom excludes every `.exec` occurrence in
the actual invocation. The same-frame theorem first rules out the spawn site;
the resulting empty descendant list then places every raw occurrence back in
the root frame. -/
theorem Exec.noExecOccurrence_of_exactMain_reachableExecFree
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) {program : Prog}
    {storageTarget codeAddress : Adr}
    (invocation :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        program storageTarget codeAddress)
    (members : List Nat)
    (accepted : program.reachableExecFree program.main members = true) :
    ∀ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      ∀ x : Xinst, occurrence.instruction ≠ .exec x := by
  apply Exec.noExecOccurrence_of_no_sameFrame_execAt run
  intro target sameFrame x execAt
  exact Exec.Deriv.noExec_of_exactMain_reachableExecFree
    invocation members accepted sameFrame x execAt

/-- Contract-neutral semantic endpoint for an exact main invocation. A
reachable exec-free certificate supplies the occurrence premise of
`Exec.noRetainedWriteTo_of_no_execOccurrence`; the distinct storage owner is
still explicit. -/
theorem Exec.noRetainedWriteTo_of_exactMain_reachableExecFree
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) {program : Prog}
    {storageTarget codeAddress owner : Adr} (key : B256)
    (invocation :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        program storageTarget codeAddress)
    (differentOwner : storageTarget ≠ owner)
    (members : List Nat)
    (accepted : program.reachableExecFree program.main members = true) :
    Exec.NoRetainedWriteTo run owner key := by
  apply Exec.noRetainedWriteTo_of_no_execOccurrence run owner key
  · rw [invocation.2.1]
    exact differentOwner
  · exact Exec.noExecOccurrence_of_exactMain_reachableExecFree
      run invocation members accepted

end Blanc
