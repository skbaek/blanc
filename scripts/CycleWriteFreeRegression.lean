import Blanc.CycleWriteFree

/-!
Concrete regression controls for cycle-safe same-frame source-level
SSTORE-occurrence freedom.  The cyclic witnesses below are actual finite
`Exec` derivations.  Their cursors are constructed directly after the
compiler's entry `JUMPDEST`; no SSTORE target is assumed to obtain them.
-/

namespace Blanc.CycleWriteFreeRegression

open Jaune Blanc

noncomputable section

/-! ## Structural checker controls and fail-closed mutants -/

private def emptyProgram : Prog :=
  ⟨.last .stop, []⟩

private def callingEmptyProgram : Prog :=
  ⟨.call 0, []⟩

private def pushPayloadProgram : Prog :=
  ⟨.next (.push [0x55] (by decide)) (.last .stop), []⟩

private def writer : Func :=
  .next (.reg .sstore) (.last .stop)

private def outsideWriterProgram : Prog :=
  ⟨.last .stop, [writer]⟩

/-- A self-loop whose zero branch reverts after one witnessed loop traversal. -/
private def selfLoopProgram : Prog :=
  ⟨.branch (.last .rev) (.call 0), []⟩

/-- A two-node cycle.  The concrete execution takes `0 → 1 → 0`, then
the second visit to node zero takes its stopping branch. -/
private def twoNodeProgram : Prog :=
  ⟨.branch (.last .stop) (.call 1),
    [.branch (.last .stop) (.call 0)]⟩

private def duplicateProgram : Prog := selfLoopProgram

private def missingLookupProgram : Prog :=
  ⟨.call 2, []⟩

private def outOfSetProgram : Prog :=
  ⟨.call 1, []⟩

private def sstoreBeforeCycleProgram : Prog :=
  ⟨.next (.reg .sstore) (.call 0), []⟩

private def selectedWriterProgram : Prog :=
  ⟨.call 1, [writer]⟩

private def possiblePostCycleWriterProgram : Prog :=
  ⟨.branch writer (.call 0), []⟩

private def recursiveWriterProgram : Prog :=
  ⟨.call 0, [.branch writer (.call 1)]⟩

private def untakenBranchWriterProgram : Prog :=
  ⟨.call 1, [.branch writer (.last .stop)]⟩

/-- Deliberately wrong lookup: it forgets that compiler-table index zero is
`program.main`. -/
private def auxOnlyFunction? (program : Prog) (index : Nat) : Option Func :=
  program.aux[index]?

private def auxOnlyComponentSstoreFree
    (program : Prog) (members : List Nat) : Bool :=
  members.all fun index =>
    match auxOnlyFunction? program index with
    | none => false
    | some body =>
        body.localSstoreFree &&
          body.callsIn (fun callee => callee ∈ members)

/-- A bounded recursive substitution for the cycle-safe checker.  Following a
source call consumes fuel, so every finite fuel rejects a genuine source
cycle. -/
private def fuelSstoreFree
    (fuel : Nat) (program : Prog) : Func → Bool
  | .last _ => true
  | .next (.reg .sstore) _ => false
  | .next _ tail => fuelSstoreFree fuel program tail
  | .branch left right =>
      fuelSstoreFree fuel program left && fuelSstoreFree fuel program right
  | .call index =>
      match fuel with
      | 0 => false
      | fuel + 1 =>
          match program.function? index with
          | none => false
          | some body => fuelSstoreFree fuel program body

private def pushPayloadContains55 : Bool :=
  match pushPayloadProgram.compile with
  | some bytes => bytes.contains 0x55
  | none => false

private def checkerControls : List Bool :=
  [ emptyProgram.entrySstoreFree emptyProgram.main []
  , !callingEmptyProgram.entrySstoreFree callingEmptyProgram.main []
  , selfLoopProgram.entrySstoreFree selfLoopProgram.main [0]
  , twoNodeProgram.entrySstoreFree twoNodeProgram.main [0, 1]
  , duplicateProgram.entrySstoreFree duplicateProgram.main [0, 0]
  , pushPayloadProgram.entrySstoreFree pushPayloadProgram.main []
  , pushPayloadContains55
  , outsideWriterProgram.entrySstoreFree outsideWriterProgram.main []
  , (twoNodeProgram.function? 0).isSome
  , (twoNodeProgram.function? 1).isSome
  , !missingLookupProgram.entrySstoreFree missingLookupProgram.main [2]
  , !outOfSetProgram.entrySstoreFree outOfSetProgram.main [0]
  , !auxOnlyComponentSstoreFree outsideWriterProgram [0]
  , !sstoreBeforeCycleProgram.entrySstoreFree
      sstoreBeforeCycleProgram.main [0]
  , !selectedWriterProgram.entrySstoreFree selectedWriterProgram.main [1]
  , !possiblePostCycleWriterProgram.entrySstoreFree
      possiblePostCycleWriterProgram.main [0]
  , !recursiveWriterProgram.entrySstoreFree recursiveWriterProgram.main [0, 1]
  , !untakenBranchWriterProgram.entrySstoreFree
      untakenBranchWriterProgram.main [1]
  , !fuelSstoreFree 8 selfLoopProgram selfLoopProgram.main
  ]

/-! ## Actual finite same-frame traces -/

/-- An explicit childless continuation chain.  Its constructors are actual
`Evm.step = .cont` equations, and `pcs` exposes their exact program-counter
sequence for evaluator pinning. -/
private inductive ContTrace (sevm : Sevm) : Nat → Devm → Type
  | refl (pc : Nat) (pre : Devm) : ContTrace sevm pc pre
  | step {pc nextPc : Nat} {pre nextPre : Devm}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont nextPc nextPre)
      (rest : ContTrace sevm nextPc nextPre) : ContTrace sevm pc pre

private def ContTrace.endPc
    {sevm : Sevm} {pc : Nat} {pre : Devm} :
    ContTrace sevm pc pre → Nat
  | .refl pc _ => pc
  | .step _ rest => rest.endPc

private def ContTrace.endPre
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) : Devm :=
  match trace with
  | .refl _ pre => pre
  | .step _ rest => rest.endPre

private def ContTrace.pcs
    {sevm : Sevm} {pc : Nat} {pre : Devm} :
    ContTrace sevm pc pre → List Nat
  | .refl pc _ => [pc]
  | .step _ rest => pc :: rest.pcs

private def buildContTrace?
    (sevm : Sevm) (pc : Nat) (pre : Devm) :
    (depth : Nat) → Option (ContTrace sevm pc pre)
  | 0 => some (.refl pc pre)
  | depth + 1 =>
      match hstep : Evm.step ⟨pc, sevm, pre⟩ with
      | .cont nextPc nextPre =>
          match buildContTrace? sevm nextPc nextPre depth with
          | some rest => some (.step hstep rest)
          | none => none
      | _ => none

private def ContTrace.out
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) : Execution :=
  exec ⟨trace.endPc, sevm, trace.endPre⟩

private def ContTrace.tail
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) :
    Exec trace.endPc sevm trace.endPre trace.out :=
  Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)

private def ContTrace.run
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) : Exec pc sevm pre trace.out :=
  match trace with
  | .refl pc pre =>
      Classical.choice ((exec_iff_exec_eq pc sevm pre
        (exec ⟨pc, sevm, pre⟩)).2 rfl)
  | .step hstep rest => .cont hstep rest.run

private def ContTrace.root
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) : Exec.Deriv :=
  ⟨pc, sevm, pre, trace.out, trace.run⟩

private def ContTrace.node
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) : Exec.Deriv :=
  ⟨trace.endPc, sevm, trace.endPre, trace.out, trace.tail⟩

private theorem ContTrace.parentPrefix
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) :
    Exec.Deriv.ParentPrefix trace.root trace.node :=
  match trace with
  | .refl _ _ => .refl _
  | .step hstep rest =>
      .step (.cont hstep rest.run) rest.parentPrefix

private theorem ContTrace.getLast?_pcs
    {sevm : Sevm} {pc : Nat} {pre : Devm}
    (trace : ContTrace sevm pc pre) :
    trace.pcs.getLast? = some trace.endPc := by
  induction trace with
  | refl => rfl
  | step hstep rest ih =>
      cases rest <;> simp_all [ContTrace.pcs, ContTrace.endPc]

private def cycleSevm (code : ByteArray) : Sevm :=
  { (default : Sevm) with code, codeAddress := some 0x600 }

private def selfLoopCode : ByteArray :=
  ByteArray.mk #[0x5b, 0x61, 0x00, 0x06, 0x57, 0xfd,
    0x5b, 0x61, 0x00, 0x00, 0x56]

private def twoNodeCode : ByteArray :=
  ByteArray.mk #[0x5b, 0x61, 0x00, 0x06, 0x57, 0x00,
    0x5b, 0x61, 0x00, 0x0b, 0x56,
    0x5b, 0x61, 0x00, 0x11, 0x57, 0x00,
    0x5b, 0x61, 0x00, 0x00, 0x56]

private def selfLoopPre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [1, 0, 0, 0]

private def twoNodePre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [1, 1, 0]

private structure CycleFixture
    (program : Prog) (code : ByteArray) (pre : Devm)
    (members : List Nat) where
  afterGlue : Devm
  entryStep : Evm.step ⟨0, cycleSevm code, pre⟩ = .cont 1 afterGlue
  trace : ContTrace (cycleSevm code) 1 afterGlue
  compiled : some code.toList = program.compile
  accepted : program.entrySstoreFree program.main members = true

private def CycleFixture.out
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) : Execution :=
  w.trace.out

private def CycleFixture.run
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) :
    Exec 0 (cycleSevm code) pre w.out :=
  .cont w.entryStep w.trace.run

private def CycleFixture.root
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) : Exec.Deriv :=
  ⟨0, cycleSevm code, pre, w.out, w.run⟩

private def CycleFixture.postCycle
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) : Exec.Deriv :=
  w.trace.node

private def cycleFixture?
    (program : Prog) (code : ByteArray) (pre : Devm)
    (members : List Nat) (cycleDepth : Nat) :
    Option (CycleFixture program code pre members) :=
  if compiled : some code.toList = program.compile then
    if accepted : program.entrySstoreFree program.main members = true then
      match entryStep : Evm.step ⟨0, cycleSevm code, pre⟩ with
      | .cont pc afterGlue =>
          if hpc : pc = 1 then
            match buildContTrace? (cycleSevm code) 1 afterGlue cycleDepth with
            | some trace => some {
                afterGlue
                entryStep := by simpa [hpc] using entryStep
                trace
                compiled
                accepted }
            | none => none
          else none
      | _ => none
    else none
  else none

private def selfLoopFixture? :
    Option (CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0]) :=
  cycleFixture? selfLoopProgram selfLoopCode selfLoopPre [0] 6

private def twoNodeFixture? :
    Option (CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1]) :=
  cycleFixture? twoNodeProgram twoNodeCode twoNodePre [0, 1] 12

private def selfLoopExecutionAvailable : Bool :=
  match selfLoopFixture? with
  | some w =>
      w.trace.pcs == [1, 4, 6, 7, 10, 0, 1] &&
        !Execution.commits w.out
  | none => false

private def twoNodeExecutionAvailable : Bool :=
  match twoNodeFixture? with
  | some w =>
      w.trace.pcs == [1, 4, 6, 7, 10, 11, 12, 15, 17, 18, 21, 0, 1] &&
        Execution.commits w.out
  | none => false

/-! ## Proof-indexed cyclic nonvacuity and universal specialization -/

private theorem CycleFixture.sourceSlice
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) :
    subcode code.toList 1
      (Func.compile (table 0 (program.main :: program.aux)) 1 program.main) := by
  have hget :
      (table 0 (program.main :: program.aux))[0]? =
        some (0, program.main) := rfl
  rcases subcode_of_get?_eq_some w.compiled hget with
    ⟨_, sourceSlice⟩
  simpa using sourceSlice

private theorem CycleFixture.sourceBoundary
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) :
    noPushBefore (cycleSevm code).code 1 32 = true := by
  have hget :
      (table 0 (program.main :: program.aux))[0]? =
        some (0, program.main) := rfl
  exact (Prog.jumpable_of_get?_table w.compiled hget).2

private def CycleFixture.cursor
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) :
    Exec.Deriv.SourceCursor w.root program ⟨0, []⟩ program.main :=
  { pc := 1
    pre := w.afterGlue
    current := w.trace.run
    parentPrefix := .step (.cont w.entryStep w.trace.run) (.refl _)
    codeSlice := w.sourceSlice
    codeBoundary := w.sourceBoundary
    sourceIncluded := by
      have hget :
          (table 0 (program.main :: program.aux))[0]? =
            some (0, program.main) := rfl
      intro site member
      simp only [Prog.sourceSites, List.mem_flatMap]
      refine ⟨0, by simp, ?_⟩
      simpa only [hget] using member }

private theorem CycleFixture.cyclePrefix
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) :
    Exec.Deriv.ParentPrefix w.cursor.node w.postCycle := by
  change Exec.Deriv.ParentPrefix w.trace.root w.trace.node
  simpa [ContTrace.root] using
    w.trace.parentPrefix

/-- Exact same-frame universal no-SSTORE specialization for a concrete cyclic
cursor.  It has no success, commitment, settlement, or termination premise. -/
private theorem CycleFixture.noSstore
    {program : Prog} {code : ByteArray} {pre : Devm} {members : List Nat}
    (w : CycleFixture program code pre members) :
    ∀ target,
      Exec.Deriv.ParentPrefix w.cursor.node target →
        ¬ Ninst.At target.sevm.code target.pc (.reg .sstore) := by
  intro target reached storeAt
  exact w.cursor.noSstore_of_entrySstoreFree w.compiled members w.accepted
    reached storeAt

private theorem functionTable_index_zero :
    twoNodeProgram.function? 0 = some twoNodeProgram.main := by
  rfl

private theorem functionTable_index_one :
    twoNodeProgram.function? 1 = twoNodeProgram.aux[0]? := by
  rfl

private theorem selfLoopFixture_nonempty :
    Nonempty (CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0]) := by
  have available : selfLoopExecutionAvailable = true := by
    native_decide
  unfold selfLoopExecutionAvailable at available
  cases fixture : selfLoopFixture? with
  | none => simp [fixture] at available
  | some witness => exact ⟨witness⟩

private theorem twoNodeFixture_nonempty :
    Nonempty (CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1]) := by
  have available : twoNodeExecutionAvailable = true := by
    native_decide
  unfold twoNodeExecutionAvailable at available
  cases fixture : twoNodeFixture? with
  | none => simp [fixture] at available
  | some witness => exact ⟨witness⟩

/-- The self-loop fixture pins the exact compiled execution, independent
cursor, cycle-spanning same-frame prefix, universal theorem application, and
noncommitting outcome after the cycle. -/
private theorem concrete_selfLoop_cycle :
    ∃ w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0],
      w.trace.pcs = [1, 4, 6, 7, 10, 0, 1] ∧
      w.postCycle.pc = 1 ∧
      Exec.Deriv.ParentPrefix w.cursor.node w.postCycle ∧
      (∀ target,
        Exec.Deriv.ParentPrefix w.cursor.node target →
          ¬ Ninst.At target.sevm.code target.pc (.reg .sstore)) ∧
      Execution.commits w.out = false := by
  have available : selfLoopExecutionAvailable = true := by native_decide
  unfold selfLoopExecutionAvailable at available
  cases fixture : selfLoopFixture? with
  | none => simp [fixture] at available
  | some w =>
  rw [fixture] at available
  simp only [Bool.and_eq_true, beq_iff_eq] at available
  have lastPc := congrArg List.getLast? available.1
  rw [w.trace.getLast?_pcs] at lastPc
  norm_num at lastPc
  have endPc : w.postCycle.pc = 1 := by
    change w.trace.endPc = 1
    exact lastPc
  exact ⟨w, available.1, endPc, w.cyclePrefix, w.noSstore,
    Bool.eq_false_of_not_eq_true (by simpa using available.2)⟩

/-- The two-node fixture pins `0 → 1 → 0`, the independently built cursor,
the cycle-spanning same-frame prefix, the universal theorem application, and a
committing outcome after the cycle. -/
private theorem concrete_twoNode_cycle :
    ∃ w : CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1],
      w.trace.pcs =
        [1, 4, 6, 7, 10, 11, 12, 15, 17, 18, 21, 0, 1] ∧
      w.postCycle.pc = 1 ∧
      Exec.Deriv.ParentPrefix w.cursor.node w.postCycle ∧
      (∀ target,
        Exec.Deriv.ParentPrefix w.cursor.node target →
          ¬ Ninst.At target.sevm.code target.pc (.reg .sstore)) ∧
      Execution.commits w.out = true := by
  have available : twoNodeExecutionAvailable = true := by native_decide
  unfold twoNodeExecutionAvailable at available
  cases fixture : twoNodeFixture? with
  | none => simp [fixture] at available
  | some w =>
  rw [fixture] at available
  simp only [Bool.and_eq_true, beq_iff_eq] at available
  have lastPc := congrArg List.getLast? available.1
  rw [w.trace.getLast?_pcs] at lastPc
  norm_num at lastPc
  have endPc : w.postCycle.pc = 1 := by
    change w.trace.endPc = 1
    exact lastPc
  exact ⟨w, available.1, endPc, w.cyclePrefix, w.noSstore, available.2⟩

/-! ## Arbitrary-outcome SSTORE occurrence controls -/

private def rootExec (sevm : Sevm) (pre : Devm) : Exec.Deriv :=
  let out := exec ⟨0, sevm, pre⟩
  let run := Classical.choice ((exec_iff_exec_eq 0 sevm pre out).2 rfl)
  ⟨0, sevm, pre, out, run⟩

private theorem rootExec_sstore_occurs
    {sevm : Sevm} {pre : Devm}
    (decoded : Ninst.At sevm.code 0 (.reg .sstore)) :
    ∃ occurrence : Exec.NinstOccurrence (rootExec sevm pre),
      occurrence.instruction = .reg .sstore := by
  have reached : rootExec sevm pre ∈
      Exec.rawNodes (rootExec sevm pre).exc :=
    Exec.mem_rawNodes_self (rootExec sevm pre).exc
  rcases Exec.exists_ninstOccurrence_of_mem_rawNodes reached decoded with
    ⟨occurrence, _, instructionEq⟩
  exact ⟨occurrence, instructionEq⟩

private def noOpSstoreCode : ByteArray := ByteArray.mk #[0x55, 0x00]
private def noOpSstoreSevm : Sevm :=
  { (default : Sevm) with code := noOpSstoreCode }
private def noOpSstorePre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [0, 0]

private def revertedSstoreCode : ByteArray :=
  ByteArray.mk #[0x55, 0x60, 0x00, 0x60, 0x00, 0xfd]
private def revertedSstoreSevm : Sevm :=
  { (default : Sevm) with code := revertedSstoreCode }
private def revertedSstorePre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [0, 1]

private def terminalErrorSstoreCode : ByteArray := ByteArray.mk #[0x55]
private def terminalErrorSstoreSevm : Sevm :=
  { (default : Sevm) with code := terminalErrorSstoreCode }
private def terminalErrorSstorePre : Devm :=
  (default : Devm).withGasLeft 100000

theorem noOp_sstore_occurs :
    (∃ occurrence : Exec.NinstOccurrence
        (rootExec noOpSstoreSevm noOpSstorePre),
      occurrence.instruction = .reg .sstore) ∧
    Execution.commits (rootExec noOpSstoreSevm noOpSstorePre).exn = true := by
  refine ⟨rootExec_sstore_occurs (by rfl), ?_⟩
  change Execution.commits (exec ⟨0, noOpSstoreSevm, noOpSstorePre⟩) = true
  native_decide

theorem reverted_sstore_occurs :
    (∃ occurrence : Exec.NinstOccurrence
        (rootExec revertedSstoreSevm revertedSstorePre),
      occurrence.instruction = .reg .sstore) ∧
    Execution.commits (rootExec revertedSstoreSevm revertedSstorePre).exn =
      false := by
  refine ⟨rootExec_sstore_occurs (by rfl), ?_⟩
  change Execution.commits
    (exec ⟨0, revertedSstoreSevm, revertedSstorePre⟩) = false
  native_decide

theorem terminalError_sstore_occurs :
    (∃ occurrence : Exec.NinstOccurrence
        (rootExec terminalErrorSstoreSevm terminalErrorSstorePre),
      occurrence.instruction = .reg .sstore) ∧
    Execution.commits
        (rootExec terminalErrorSstoreSevm terminalErrorSstorePre).exn = false := by
  refine ⟨rootExec_sstore_occurs (by rfl), ?_⟩
  change Execution.commits
    (exec ⟨0, terminalErrorSstoreSevm, terminalErrorSstorePre⟩) = false
  native_decide

/-! ## Child-frame non-claim controls -/

private theorem parentPrefix_sevm_eq {root tail : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root tail) :
    root.sevm = tail.sevm := by
  induction hprefix with
  | refl => rfl
  | step head rest ih => cases head <;> simpa using ih

namespace ExternalChild

private def target : Adr := 0x700
private def parentProgram : Prog := ⟨.last .stop, []⟩
private def parentCode : ByteArray := ByteArray.mk #[0xf1, 0x00]
private def childCode : ByteArray := ByteArray.mk #[0x55, 0x00]
private def parentSevm : Sevm :=
  { (default : Sevm) with code := parentCode }
private def parentPre : Devm :=
  let pre := ((default : Devm).withGasLeft 100000).withStack
    [50000, target.toB256, 0, 0, 0, 0, 0]
  pre.withState (pre.state.setCode target childCode)

private structure Fixture where
  nextPc : Nat
  resumed : Devm
  frame : Jaune.Frame
  resume : Resume
  childEvm : Evm
  raw : Execution
  out : Execution
  hstep : Evm.step ⟨0, parentSevm, parentPre⟩ =
    .spawn frame resume nextPc
  henter : frame.enter = .run childEvm
  child : Exec childEvm.pc childEvm.sta childEvm.dyna raw
  hresume : resume.run (frame.settle raw) = .ok resumed
  next : Exec nextPc parentSevm resumed out
  childPc : childEvm.pc = 0
  childCodeEq : childEvm.sta.code = childCode

private def Fixture.run (w : Fixture) : Exec 0 parentSevm parentPre w.out :=
  .runOk w.hstep w.henter w.child w.hresume w.next

private def Fixture.root (w : Fixture) : Exec.Deriv :=
  ⟨0, parentSevm, parentPre, w.out, w.run⟩

private def Fixture.childRoot (w : Fixture) : Exec.Deriv :=
  ⟨w.childEvm.pc, w.childEvm.sta, w.childEvm.dyna, w.raw, w.child⟩

private def fixture? : Option Fixture :=
  match hstep : Evm.step ⟨0, parentSevm, parentPre⟩ with
  | .spawn frame resume nextPc =>
      match henter : frame.enter with
      | .run childEvm =>
          let raw := exec childEvm
          match hresume : resume.run (frame.settle raw) with
          | .ok resumed =>
              let out := exec ⟨nextPc, parentSevm, resumed⟩
              let child := Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
              let next := Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
              if childPc : childEvm.pc = 0 then
              if childCodeEq : childEvm.sta.code = childCode then
                some {
                  nextPc := nextPc
                  resumed := resumed
                  frame := frame
                  resume := resume
                  childEvm := childEvm
                  raw := raw
                  out := out
                  hstep := hstep
                  henter := henter
                  child := child
                  hresume := hresume
                  next := next
                  childPc := childPc
                  childCodeEq := childCodeEq }
              else none
              else none
          | .error _ => none
      | .done _ => none
  | _ => none

private def available : Bool :=
  match Evm.step ⟨0, parentSevm, parentPre⟩ with
  | .spawn frame resume _ =>
      match frame.enter with
      | .run childEvm =>
          childEvm.pc == 0 && decide (childEvm.sta.code = childCode) &&
            match resume.run (frame.settle (exec childEvm)) with
            | .ok _ => true
            | .error _ => false
      | .done _ => false
  | _ => false

private theorem fixture_nonempty : Nonempty Fixture := by
  have h : available = true := by native_decide
  unfold available at h
  cases hstep : Evm.step ⟨0, parentSevm, parentPre⟩ with
  | spawn frame resume nextPc =>
    cases henter : frame.enter with
    | run childEvm =>
      cases hresume : resume.run (frame.settle (exec childEvm)) with
      | ok resumed =>
        simp only [hstep, henter, hresume, Bool.and_eq_true,
          beq_iff_eq] at h
        let raw := exec childEvm
        let out := exec ⟨nextPc, parentSevm, resumed⟩
        let child : Exec childEvm.pc childEvm.sta childEvm.dyna raw :=
          Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
        let next : Exec nextPc parentSevm resumed out :=
          Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
        exact ⟨{
          nextPc := nextPc
          resumed := resumed
          frame := frame
          resume := resume
          childEvm := childEvm
          raw := raw
          out := out
          hstep := hstep
          henter := henter
          child := child
          hresume := by simpa [raw] using hresume
          next := next
          childPc := h.1.1
          childCodeEq := of_decide_eq_true h.1.2 }⟩
      | error error => simp [hstep, henter, hresume] at h
    | done settled => simp [hstep, henter] at h
  | halt result => simp [hstep] at h
  | cont pc post => simp [hstep] at h

private theorem Fixture.child_not_parent_prefix (w : Fixture) :
    ¬ Exec.Deriv.ParentPrefix w.root w.childRoot := by
  intro hprefix
  have sameCode := congrArg (fun sevm : Sevm => sevm.code)
    (parentPrefix_sevm_eq hprefix)
  change parentCode = w.childEvm.sta.code at sameCode
  rw [w.childCodeEq] at sameCode
  exact (by native_decide : parentCode ≠ childCode) sameCode

private theorem Fixture.child_sstore (w : Fixture) :
    ∃ occurrence : Exec.NinstOccurrence w.root,
      occurrence.instruction = .reg .sstore ∧
      Exec.Deriv.ParentPrefix w.childRoot occurrence.node ∧
      ¬ Exec.Deriv.ParentPrefix w.root occurrence.node := by
  have childSelected : w.childRoot ∈ Exec.rawFrameRoots w.run := by
    simp [Fixture.run, Fixture.childRoot, Exec.rawFrameRoots,
      Exec.rawFrameDescendants]
  have decoded : Ninst.At w.childRoot.sevm.code w.childRoot.pc
      (.reg .sstore) := by
    change Ninst.At w.childEvm.sta.code w.childEvm.pc (.reg .sstore)
    rw [w.childPc, w.childCodeEq]
    rfl
  have global : w.childRoot ∈ Exec.rawNodes w.run :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix w.run w.childRoot).mpr
      ⟨w.childRoot, childSelected, .refl _⟩
  rcases Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := w.root) global decoded with
    ⟨occurrence, nodeEq, instructionEq⟩
  refine ⟨occurrence, instructionEq, by simpa [nodeEq] using
    (Exec.Deriv.ParentPrefix.refl w.childRoot), ?_⟩
  intro hprefix
  apply w.child_not_parent_prefix
  simpa [nodeEq] using hprefix

theorem control :
    ∃ w : Fixture,
      w.childRoot ∈ Exec.rawFrameRoots w.run ∧
      (∃ occurrence : Exec.NinstOccurrence w.root,
        occurrence.instruction = .reg .sstore ∧
        Exec.Deriv.ParentPrefix w.childRoot occurrence.node ∧
        ¬ Exec.Deriv.ParentPrefix w.root occurrence.node) := by
  rcases fixture_nonempty with ⟨w⟩
  refine ⟨w, ?_, w.child_sstore⟩
  simp [Fixture.run, Fixture.childRoot, Exec.rawFrameRoots,
    Exec.rawFrameDescendants]

theorem false_all_frame_refuted :
    ¬ (∀ w : Fixture, ∀ occurrence : Exec.NinstOccurrence w.root,
      occurrence.instruction = .reg .sstore →
        Exec.Deriv.ParentPrefix w.root occurrence.node) := by
  rintro falseClaim
  rcases control with ⟨w, _, occurrence, isStore, _, notOwned⟩
  exact notOwned (falseClaim w occurrence isStore)

end ExternalChild

namespace SameOwnerChild

/-! CALLCODE executes another account's code against the parent's storage
owner. This is the sharp counterexample to any endpoint-storage conclusion:
the child is outside the parent source cursor even though both frames have the
same `currentTarget`. -/

private def owner : Adr := 0x600
private def target : Adr := 0x700
private def parentCode : ByteArray := ByteArray.mk #[0xf2, 0x00]
private def childCode : ByteArray :=
  ByteArray.mk #[0x60, 0x01, 0x60, 0x00, 0x55, 0x00]
private def parentSevm : Sevm :=
  { (default : Sevm) with
    code := parentCode
    currentTarget := owner
    codeAddress := some owner }
private def parentPre : Devm :=
  let pre := ((default : Devm).withGasLeft 100000).withStack
    [50000, target.toB256, 0, 0, 0, 0, 0]
  pre.withState (pre.state.setCode target childCode)

private structure Fixture where
  nextPc : Nat
  resumed : Devm
  frame : Jaune.Frame
  resume : Resume
  childEvm : Evm
  raw : Execution
  out : Execution
  hstep : Evm.step ⟨0, parentSevm, parentPre⟩ =
    .spawn frame resume nextPc
  henter : frame.enter = .run childEvm
  child : Exec childEvm.pc childEvm.sta childEvm.dyna raw
  hresume : resume.run (frame.settle raw) = .ok resumed
  next : Exec nextPc parentSevm resumed out
  childPc : childEvm.pc = 0
  childCodeEq : childEvm.sta.code = childCode
  sameOwner : childEvm.sta.currentTarget = parentSevm.currentTarget
  childCommits : Execution.commits raw = true
  parentCommits : Execution.commits out = true
  afterValue : Devm
  afterKey : Devm
  valueStep : Evm.step childEvm = .cont 2 afterValue
  keyStep : Evm.step ⟨2, childEvm.sta, afterValue⟩ = .cont 4 afterKey
  storageChanged :
    (Devm.getStor parentPre owner).get 0 ≠
      (Devm.getStor resumed owner).get 0

private def Fixture.run (w : Fixture) : Exec 0 parentSevm parentPre w.out :=
  .runOk w.hstep w.henter w.child w.hresume w.next

private def Fixture.root (w : Fixture) : Exec.Deriv :=
  ⟨0, parentSevm, parentPre, w.out, w.run⟩

private def Fixture.childRoot (w : Fixture) : Exec.Deriv :=
  ⟨w.childEvm.pc, w.childEvm.sta, w.childEvm.dyna, w.raw, w.child⟩

private def available : Bool :=
  match Evm.step ⟨0, parentSevm, parentPre⟩ with
  | .spawn frame resume nextPc =>
      match frame.enter with
      | .run childEvm =>
          match Evm.step childEvm with
          | .cont valuePc afterValue =>
              match Evm.step ⟨2, childEvm.sta, afterValue⟩ with
              | .cont keyPc _ =>
                  let raw := exec childEvm
                  match resume.run (frame.settle raw) with
                  | .ok resumed =>
                      let out := exec ⟨nextPc, parentSevm, resumed⟩
                      valuePc == 2 && keyPc == 4 && childEvm.pc == 0 &&
                        decide (childEvm.sta.code = childCode) &&
                        childEvm.sta.currentTarget ==
                          parentSevm.currentTarget &&
                        Execution.commits raw && Execution.commits out &&
                        decide ((Devm.getStor parentPre owner).get 0 ≠
                          (Devm.getStor resumed owner).get 0)
                  | .error _ => false
              | _ => false
          | _ => false
      | .done _ => false
  | _ => false

private theorem fixture_nonempty : Nonempty Fixture := by
  have h : available = true := by native_decide
  unfold available at h
  cases hstep : Evm.step ⟨0, parentSevm, parentPre⟩ with
  | spawn frame resume nextPc =>
    cases henter : frame.enter with
    | run childEvm =>
      cases valueStep : Evm.step childEvm with
      | cont valuePc afterValue =>
        cases keyStep : Evm.step ⟨2, childEvm.sta, afterValue⟩ with
        | cont keyPc afterKey =>
          let raw := exec childEvm
          cases hresume : resume.run (frame.settle raw) with
          | ok resumed =>
            let out := exec ⟨nextPc, parentSevm, resumed⟩
            simp only [hstep, henter, valueStep, keyStep] at h
            change resume.run (frame.settle (exec childEvm)) = .ok resumed
              at hresume
            rw [hresume] at h
            simp only [Bool.and_eq_true, decide_eq_true_eq,
              beq_iff_eq] at h
            let child : Exec childEvm.pc childEvm.sta childEvm.dyna raw :=
              Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
            let next : Exec nextPc parentSevm resumed out :=
              Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
            exact ⟨{
              nextPc
              resumed
              frame
              resume
              childEvm
              raw
              out
              hstep
              henter
              child
              hresume := by simpa [raw] using hresume
              next
              childPc := h.1.1.1.1.1.2
              childCodeEq := h.1.1.1.1.2
              sameOwner := h.1.1.1.2
              childCommits := h.1.1.2
              parentCommits := h.1.2
              afterValue
              afterKey
              valueStep := by simpa [h.1.1.1.1.1.1.1] using valueStep
              keyStep := by simpa [h.1.1.1.1.1.1.2] using keyStep
              storageChanged := h.2 }⟩
          | error error => simp [hstep, henter, valueStep, keyStep, hresume, raw] at h
        | halt result => simp [hstep, henter, valueStep, keyStep] at h
        | spawn f r pc => simp [hstep, henter, valueStep, keyStep] at h
      | halt result => simp [hstep, henter, valueStep] at h
      | spawn f r pc => simp [hstep, henter, valueStep] at h
    | done settled => simp [hstep, henter] at h
  | halt result => simp [hstep] at h
  | cont pc post => simp [hstep] at h

private theorem Fixture.child_not_parent_prefix (w : Fixture) :
    ¬ Exec.Deriv.ParentPrefix w.root w.childRoot := by
  intro hprefix
  have sameCode := congrArg (fun sevm : Sevm => sevm.code)
    (parentPrefix_sevm_eq hprefix)
  change parentCode = w.childEvm.sta.code at sameCode
  rw [w.childCodeEq] at sameCode
  exact (by native_decide : parentCode ≠ childCode) sameCode

private theorem Fixture.child_sstore (w : Fixture) :
    ∃ occurrence : Exec.NinstOccurrence w.root,
      occurrence.instruction = .reg .sstore ∧
      Exec.Deriv.ParentPrefix w.childRoot occurrence.node ∧
      ¬ Exec.Deriv.ParentPrefix w.root occurrence.node := by
  have childSelected : w.childRoot ∈ Exec.rawFrameRoots w.run := by
    simp [Fixture.run, Fixture.childRoot, Exec.rawFrameRoots,
      Exec.rawFrameDescendants]
  rcases (Exec.Deriv.ParentPrefix.refl w.childRoot).advance_cont
      w.child w.valueStep with ⟨atTwo, edgeTwo, prefixTwo⟩
  rcases prefixTwo.advance_cont atTwo w.keyStep with
    ⟨atFour, edgeFour, prefixFour⟩
  let node : Exec.Deriv :=
    ⟨4, w.childEvm.sta, w.afterKey, w.raw, atFour⟩
  have decoded : Ninst.At node.sevm.code node.pc (.reg .sstore) := by
    change Ninst.At w.childEvm.sta.code 4 (.reg .sstore)
    rw [w.childCodeEq]
    rfl
  have reachedChild : Exec.Deriv.ParentPrefix w.childRoot node := by
    simpa [node, Fixture.childRoot] using prefixFour
  have childNode : node ∈ Exec.rawNodes w.run :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix w.run node).mpr
      ⟨w.childRoot, childSelected, reachedChild⟩
  rcases Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := w.root) childNode decoded with
    ⟨occurrence, nodeEq, instructionEq⟩
  refine ⟨occurrence, instructionEq, ?_, ?_⟩
  · simpa [nodeEq] using reachedChild
  · intro hprefix
    have sameCode := congrArg (fun sevm : Sevm => sevm.code)
      (parentPrefix_sevm_eq hprefix)
    change parentCode = occurrence.node.sevm.code at sameCode
    rw [nodeEq] at sameCode
    change parentCode = w.childEvm.sta.code at sameCode
    rw [w.childCodeEq] at sameCode
    exact (by native_decide : parentCode ≠ childCode) sameCode

theorem control :
    ∃ w : Fixture,
      w.childRoot.sevm.currentTarget = w.root.sevm.currentTarget ∧
      Execution.commits w.raw = true ∧
      Execution.commits w.out = true ∧
      (Devm.getStor parentPre owner).get 0 ≠
        (Devm.getStor w.resumed owner).get 0 ∧
      (∃ occurrence : Exec.NinstOccurrence w.root,
        occurrence.instruction = .reg .sstore ∧
        Exec.Deriv.ParentPrefix w.childRoot occurrence.node ∧
        ¬ Exec.Deriv.ParentPrefix w.root occurrence.node) := by
  rcases fixture_nonempty with ⟨w⟩
  refine ⟨w, w.sameOwner, w.childCommits, w.parentCommits,
    w.storageChanged, w.child_sstore⟩

theorem storage_equality_refuted :
    ¬ (∀ w : Fixture,
      Execution.commits w.raw = true →
      Execution.commits w.out = true →
      (Devm.getStor parentPre owner).get 0 =
        (Devm.getStor w.resumed owner).get 0) := by
  rintro falseClaim
  rcases control with ⟨w, _, childCommits, parentCommits,
    storageChanged, _⟩
  exact storageChanged (falseClaim w childCommits parentCommits)

end SameOwnerChild

/-! ## Gate-facing positive declarations -/

theorem local_checker_controls :
    emptyProgram.main.localSstoreFree = true ∧
      callingEmptyProgram.main.localSstoreFree = true ∧
      pushPayloadProgram.main.localSstoreFree = true ∧
      writer.localSstoreFree = false := by
  native_decide

theorem function_table_index_controls :
    twoNodeProgram.function? 0 = some twoNodeProgram.main ∧
      twoNodeProgram.function? 1 = twoNodeProgram.aux[0]? := by
  exact ⟨functionTable_index_zero, functionTable_index_one⟩

theorem component_checker_controls :
    selfLoopProgram.componentSstoreFree [0] = true ∧
      twoNodeProgram.componentSstoreFree [0, 1] = true ∧
      missingLookupProgram.componentSstoreFree [2] = false ∧
      outOfSetProgram.componentSstoreFree [0] = false := by
  native_decide

theorem empty_gateway_controls :
    emptyProgram.entrySstoreFree emptyProgram.main [] = true ∧
      callingEmptyProgram.entrySstoreFree callingEmptyProgram.main [] = false := by
  native_decide

theorem duplicate_member_controls :
    duplicateProgram.entrySstoreFree duplicateProgram.main [0, 0] = true ∧
      duplicateProgram.entrySstoreFree duplicateProgram.main [0] = true := by
  native_decide

theorem selfLoop_exact_execution :
    ∃ w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0],
      some selfLoopCode.toList = selfLoopProgram.compile ∧
      Nonempty (Exec 0 (cycleSevm selfLoopCode) selfLoopPre w.out) ∧
      w.trace.pcs = [1, 4, 6, 7, 10, 0, 1] := by
  rcases concrete_selfLoop_cycle with ⟨w, pcs, _⟩
  exact ⟨w, w.compiled, ⟨w.run⟩, pcs⟩

theorem selfLoop_cursor_control :
    ∃ w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0],
      Nonempty (Exec.Deriv.SourceCursor w.root selfLoopProgram
        ⟨0, []⟩ selfLoopProgram.main) := by
  rcases selfLoopFixture_nonempty with ⟨w⟩
  exact ⟨w, ⟨w.cursor⟩⟩

theorem selfLoop_cycle_prefix_control :
    ∃ w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0],
      w.trace.pcs = [1, 4, 6, 7, 10, 0, 1] ∧
      w.postCycle.pc = 1 ∧
      Exec.Deriv.ParentPrefix w.cursor.node w.postCycle := by
  rcases concrete_selfLoop_cycle with ⟨w, pcs, pc, hprefix, _⟩
  exact ⟨w, pcs, pc, hprefix⟩

theorem selfLoop_no_sstore_control :
    ∃ w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0],
      ∀ target,
        Exec.Deriv.ParentPrefix w.cursor.node target →
          ¬ Ninst.At target.sevm.code target.pc (.reg .sstore) := by
  rcases concrete_selfLoop_cycle with ⟨w, _, _, _, safe, _⟩
  exact ⟨w, safe⟩

theorem twoNode_exact_execution :
    ∃ w : CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1],
      some twoNodeCode.toList = twoNodeProgram.compile ∧
      Nonempty (Exec 0 (cycleSevm twoNodeCode) twoNodePre w.out) ∧
      w.trace.pcs =
        [1, 4, 6, 7, 10, 11, 12, 15, 17, 18, 21, 0, 1] := by
  rcases concrete_twoNode_cycle with ⟨w, pcs, _⟩
  exact ⟨w, w.compiled, ⟨w.run⟩, pcs⟩

theorem twoNode_cursor_control :
    ∃ w : CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1],
      Nonempty (Exec.Deriv.SourceCursor w.root twoNodeProgram
        ⟨0, []⟩ twoNodeProgram.main) := by
  rcases twoNodeFixture_nonempty with ⟨w⟩
  exact ⟨w, ⟨w.cursor⟩⟩

theorem twoNode_cycle_prefix_control :
    ∃ w : CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1],
      w.trace.pcs =
        [1, 4, 6, 7, 10, 11, 12, 15, 17, 18, 21, 0, 1] ∧
      w.postCycle.pc = 1 ∧
      Exec.Deriv.ParentPrefix w.cursor.node w.postCycle := by
  rcases concrete_twoNode_cycle with ⟨w, pcs, pc, hprefix, _⟩
  exact ⟨w, pcs, pc, hprefix⟩

theorem twoNode_no_sstore_control :
    ∃ w : CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1],
      ∀ target,
        Exec.Deriv.ParentPrefix w.cursor.node target →
          ¬ Ninst.At target.sevm.code target.pc (.reg .sstore) := by
  rcases concrete_twoNode_cycle with ⟨w, _, _, _, safe, _⟩
  exact ⟨w, safe⟩

theorem cyclic_outcome_controls :
    (∃ w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0],
      Exec.Deriv.ParentPrefix w.cursor.node w.postCycle ∧
        Execution.commits w.out = false) ∧
    (∃ w : CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1],
      Exec.Deriv.ParentPrefix w.cursor.node w.postCycle ∧
        Execution.commits w.out = true) := by
  rcases concrete_selfLoop_cycle with ⟨self, _, _, selfPrefix, _, selfOut⟩
  rcases concrete_twoNode_cycle with ⟨two, _, _, twoPrefix, _, twoOut⟩
  exact ⟨⟨self, selfPrefix, selfOut⟩, ⟨two, twoPrefix, twoOut⟩⟩

theorem required_positive_controls : True := by
  let _local := local_checker_controls
  let _indices := function_table_index_controls
  let _component := component_checker_controls
  let _empty := empty_gateway_controls
  let _duplicate := duplicate_member_controls
  let _selfExec := selfLoop_exact_execution
  let _selfCursor := selfLoop_cursor_control
  let _selfPrefix := selfLoop_cycle_prefix_control
  let _selfSafe := selfLoop_no_sstore_control
  let _twoExec := twoNode_exact_execution
  let _twoCursor := twoNode_cursor_control
  let _twoPrefix := twoNode_cycle_prefix_control
  let _twoSafe := twoNode_no_sstore_control
  let _outcomes := cyclic_outcome_controls
  let _noOp := noOp_sstore_occurs
  let _reverted := reverted_sstore_occurs
  let _terminal := terminalError_sstore_occurs
  let _external := ExternalChild.control
  let _allFrame := ExternalChild.false_all_frame_refuted
  let _sameOwner := SameOwnerChild.control
  let _storageBoundary := SameOwnerChild.storage_equality_refuted
  exact True.intro

-- ENTRY-LINKAGE-MUTANT-CONTROL
-- MISSING-LOOKUP-MUTANT-CONTROL
-- OUT-OF-COMPONENT-MUTANT-CONTROL
-- BODY-SUBSTITUTION-MUTANT-CONTROL
-- INDEX-SUBSTITUTION-MUTANT-CONTROL
-- OFF-BY-ONE-LOOKUP-MUTANT-CONTROL
-- PRE-CYCLE-SSTORE-MUTANT-CONTROL
-- POST-CYCLE-SSTORE-MUTANT-CONTROL
-- SELECTED-MEMBER-SSTORE-MUTANT-CONTROL
-- RECURSIVE-WRITER-MUTANT-CONTROL
-- UNTAKEN-BRANCH-WRITER-MUTANT-CONTROL
-- FUEL-RECURSIVE-SUBSTITUTION-MUTANT-CONTROL
-- RAW-BYTE-SCAN-MUTANT-CONTROL
-- WRONG-SOURCE-BODY-MUTANT-CONTROL
-- EXTERNAL-CHILD-ALL-FRAME-MUTANT-CONTROL
-- NOOP-SSTORE-PRUNE-MUTANT-CONTROL
-- REVERTED-SSTORE-PRUNE-MUTANT-CONTROL
-- TERMINAL-ERROR-SSTORE-PRUNE-MUTANT-CONTROL
-- SAME-OWNER-ENDPOINT-EQUALITY-MUTANT-CONTROL

-- The gate requires every entry in this exact vector to evaluate to `true`.
#eval! checkerControls ++
  [selfLoopExecutionAvailable, twoNodeExecutionAvailable,
    ExternalChild.available, SameOwnerChild.available]

end

end Blanc.CycleWriteFreeRegression
