import Blanc.ExecutionOccurrence

/-!
Concrete regression controls for the common execution-occurrence foundation.
Every execution fixture starts from `exec`; proof-indexed witnesses use the
canonical `exec_iff_exec_eq` bridge rather than a disconnected predicate.
-/

namespace Blanc.ExecutionOccurrenceRegression

open Jaune Blanc

noncomputable section

/-- A concrete root SSTORE which successfully continues into the rest of an
actual finite execution. -/
private structure RootSstoreFixture where
  sevm : Sevm
  before : Devm
  after : Devm
  nextPc : Nat
  out : Execution
  step : Evm.step ⟨0, sevm, before⟩ = .cont nextPc after
  next : Exec nextPc sevm after out
  decoded : Ninst.At sevm.code 0 (.reg .sstore)

private def RootSstoreFixture.run (w : RootSstoreFixture) :
    Exec 0 w.sevm w.before w.out :=
  Exec.cont w.step w.next

private def RootSstoreFixture.root (w : RootSstoreFixture) : Exec.Deriv :=
  ⟨0, w.sevm, w.before, w.out, w.run⟩

private def RootSstoreFixture.occurrence (w : RootSstoreFixture) :
    Exec.NinstOccurrence w.root :=
  { node := w.root
    instruction := .reg .sstore
    slot := .none
    stepResult := .ok w.after
    reached := Exec.mem_rawNodes_self w.run
    decoded := w.decoded
    filled := trivial
    stepRun := by
      change Ninst.StepRun 0 w.sevm w.before (.reg .sstore)
        .none (.ok w.after)
      unfold Ninst.StepRun
      rw [← Evm.step_next w.decoded, w.step]
      exact ⟨rfl, rfl⟩ }

private theorem RootSstoreFixture.successful (w : RootSstoreFixture) :
    Nonempty (Exec.SuccessfulSstoreOccurrence w.root) := by
  rcases w.occurrence.toSuccessfulSstore rfl rfl with ⟨write, _⟩
  exact ⟨write⟩

private def rootSstoreFixture? (sevm : Sevm) (before : Devm)
    (decoded : Ninst.At sevm.code 0 (.reg .sstore)) :
    Option RootSstoreFixture :=
  match step : Evm.step ⟨0, sevm, before⟩ with
  | .cont nextPc after =>
      let out := exec ⟨nextPc, sevm, after⟩
      let next := Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
      some { sevm, before, after, nextPc, out, step, next, decoded }
  | _ => none

private def rootSstoreAvailable (sevm : Sevm) (before : Devm) : Bool :=
  match Evm.getInst ⟨0, sevm, before⟩,
      Evm.step ⟨0, sevm, before⟩ with
  | some (.next (.reg .sstore)), .cont _ _ => true
  | _, _ => false

private def terminalErrorCode : ByteArray := ByteArray.mk #[0x55]
private def terminalErrorSevm : Sevm :=
  { (default : Sevm) with code := terminalErrorCode }
private def terminalErrorPre : Devm :=
  (default : Devm).withGasLeft 100000

private structure TerminalFixture where
  err : EvmError × Devm
  hstep : Evm.step ⟨0, terminalErrorSevm, terminalErrorPre⟩ =
    .halt (.error err)

private def TerminalFixture.run (w : TerminalFixture) :
    Exec 0 terminalErrorSevm terminalErrorPre (.error w.err) :=
  .halt w.hstep

private def TerminalFixture.root (w : TerminalFixture) : Exec.Deriv :=
  ⟨0, terminalErrorSevm, terminalErrorPre, .error w.err, w.run⟩

private def TerminalFixture.occurrence (w : TerminalFixture) :
    Exec.NinstOccurrence w.root :=
  { node := w.root
    instruction := .reg .sstore
    slot := .none
    stepResult := .error w.err
    reached := Exec.mem_rawNodes_self w.run
    decoded := by
      change Ninst.At terminalErrorSevm.code 0 (.reg .sstore)
      rfl
    filled := trivial
    stepRun := by
      change Ninst.StepRun 0 terminalErrorSevm terminalErrorPre
        (.reg .sstore) .none (.error w.err)
      unfold Ninst.StepRun
      rw [← Evm.step_next
        (show Ninst.At terminalErrorSevm.code 0 (.reg .sstore) by rfl),
        w.hstep]
      exact ⟨rfl, rfl⟩ }

private def terminalFixture? : Option TerminalFixture :=
  match hstep : Evm.step ⟨0, terminalErrorSevm, terminalErrorPre⟩ with
  | .halt (.error err) => some { err, hstep }
  | _ => none

/-- An `Ninst` whose own step terminates in error remains a raw occurrence. -/
private theorem terminalError_occurs (fixture : TerminalFixture) :
    fixture.occurrence.instruction = .reg .sstore ∧
      fixture.occurrence.stepResult = .error fixture.err ∧
      Exec.rawNodes fixture.run = [fixture.root] := by
  exact ⟨rfl, rfl, by simp [TerminalFixture.run, TerminalFixture.root,
    Exec.rawNodes]⟩

private def noOpCode : ByteArray := ByteArray.mk #[0x55, 0x00]
private def noOpSevm : Sevm :=
  { (default : Sevm) with code := noOpCode }
private def noOpPre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [0, 0]
private def noOpFixture? : Option RootSstoreFixture :=
  rootSstoreFixture? noOpSevm noOpPre (by rfl)

private def revertCode : ByteArray :=
  ByteArray.mk #[0x55, 0x60, 0x00, 0x60, 0x00, 0xfd]
private def revertSevm : Sevm :=
  { (default : Sevm) with code := revertCode }
private def revertPre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [0, 1]
private def revertFixture? : Option RootSstoreFixture :=
  rootSstoreFixture? revertSevm revertPre (by rfl)

private def laterOogCode : ByteArray := ByteArray.mk #[0x55, 0x54, 0x00]
private def laterOogSevm : Sevm :=
  { (default : Sevm) with code := laterOogCode }
private def laterOogPre : Devm :=
  ((default : Devm).withGasLeft 22100).withStack [0, 1, 0]
private def laterOogFixture? : Option RootSstoreFixture :=
  rootSstoreFixture? laterOogSevm laterOogPre (by rfl)

/-- The no-op, later-REVERT and later-OOG fixtures all contain an actual
successful root SSTORE occurrence. -/
private theorem rootWriteControls
    (_noOp : noOpFixture? = some noOpFixture)
    (_reverted : revertFixture? = some revertFixture)
    (_laterOog : laterOogFixture? = some laterOogFixture) :
    Nonempty (Exec.SuccessfulSstoreOccurrence noOpFixture.root) ∧
      Nonempty (Exec.SuccessfulSstoreOccurrence revertFixture.root) ∧
      Nonempty (Exec.SuccessfulSstoreOccurrence laterOogFixture.root) := by
  exact ⟨noOpFixture.successful, revertFixture.successful,
    laterOogFixture.successful⟩

/-- Concrete multi-write history: 5, then 7, then a no-op 7 to the same cell. -/
private def historyCode : ByteArray := ByteArray.mk #[
  0x60, 0x05, 0x60, 0x00, 0x55,
  0x60, 0x07, 0x60, 0x00, 0x55,
  0x60, 0x07, 0x60, 0x00, 0x55, 0x00]
private def historySevm : Sevm :=
  { (default : Sevm) with code := historyCode }
private def historyPre : Devm := (default : Devm).withGasLeft 100000

private structure HistoryFixture where
  s2 : Devm
  s4 : Devm
  s5 : Devm
  s7 : Devm
  s9 : Devm
  s10 : Devm
  s12 : Devm
  s14 : Devm
  s15 : Devm
  out : Execution
  h0 : Evm.step ⟨0, historySevm, historyPre⟩ = .cont 2 s2
  h2 : Evm.step ⟨2, historySevm, s2⟩ = .cont 4 s4
  h4 : Evm.step ⟨4, historySevm, s4⟩ = .cont 5 s5
  h5 : Evm.step ⟨5, historySevm, s5⟩ = .cont 7 s7
  h7 : Evm.step ⟨7, historySevm, s7⟩ = .cont 9 s9
  h9 : Evm.step ⟨9, historySevm, s9⟩ = .cont 10 s10
  h10 : Evm.step ⟨10, historySevm, s10⟩ = .cont 12 s12
  h12 : Evm.step ⟨12, historySevm, s12⟩ = .cont 14 s14
  h14 : Evm.step ⟨14, historySevm, s14⟩ = .cont 15 s15
  h15 : Evm.step ⟨15, historySevm, s15⟩ = .halt out
  commits : Execution.commits out = true
  changed :
    (Devm.getStor historyPre historySevm.currentTarget).get 0 ≠
      (Devm.getStor (Execution.committedPost out commits)
        historySevm.currentTarget).get 0
  finalValue :
    (Devm.getStor (Execution.committedPost out commits)
      historySevm.currentTarget).get 0 = 7
  stack4 : s4.stack = [0, 5]
  stack9 : s9.stack = [0, 7]
  stack14 : s14.stack = [0, 7]

private def HistoryFixture.run (w : HistoryFixture) :
    Exec 0 historySevm historyPre w.out :=
  .cont w.h0 (.cont w.h2 (.cont w.h4 (.cont w.h5 (.cont w.h7
    (.cont w.h9 (.cont w.h10 (.cont w.h12 (.cont w.h14
      (.halt w.h15)))))))))

private def HistoryFixture.root (w : HistoryFixture) : Exec.Deriv :=
  ⟨0, historySevm, historyPre, w.out, w.run⟩

private def HistoryFixture.node14 (w : HistoryFixture) : Exec.Deriv :=
  ⟨14, historySevm, w.s14, w.out, .cont w.h14 (.halt w.h15)⟩

private def HistoryFixture.occurrence14 (w : HistoryFixture) :
    Exec.NinstOccurrence w.root :=
  { node := w.node14
    instruction := .reg .sstore
    slot := .none
    stepResult := .ok w.s15
    reached := by
      simp [HistoryFixture.root, HistoryFixture.run, HistoryFixture.node14,
        Exec.rawNodes]
    decoded := by
      change Ninst.At historySevm.code 14 (.reg .sstore)
      rfl
    filled := trivial
    stepRun := by
      change Ninst.StepRun 14 historySevm w.s14 (.reg .sstore)
        .none (.ok w.s15)
      unfold Ninst.StepRun
      rw [← Evm.step_next
        (show Ninst.At historySevm.code 14 (.reg .sstore) by rfl), w.h14]
      exact ⟨rfl, rfl⟩ }

private def historyFixture? : Option HistoryFixture :=
  match h0 : Evm.step ⟨0, historySevm, historyPre⟩ with
  | .cont pc2 s2 => if hp2 : pc2 = 2 then
    match h2 : Evm.step ⟨2, historySevm, s2⟩ with
    | .cont pc4 s4 => if hp4 : pc4 = 4 then
      match h4 : Evm.step ⟨4, historySevm, s4⟩ with
      | .cont pc5 s5 => if hp5 : pc5 = 5 then
        match h5 : Evm.step ⟨5, historySevm, s5⟩ with
        | .cont pc7 s7 => if hp7 : pc7 = 7 then
          match h7 : Evm.step ⟨7, historySevm, s7⟩ with
          | .cont pc9 s9 => if hp9 : pc9 = 9 then
            match h9 : Evm.step ⟨9, historySevm, s9⟩ with
            | .cont pc10 s10 => if hp10 : pc10 = 10 then
              match h10 : Evm.step ⟨10, historySevm, s10⟩ with
              | .cont pc12 s12 => if hp12 : pc12 = 12 then
                match h12 : Evm.step ⟨12, historySevm, s12⟩ with
                | .cont pc14 s14 => if hp14 : pc14 = 14 then
                  match h14 : Evm.step ⟨14, historySevm, s14⟩ with
                  | .cont pc15 s15 => if hp15 : pc15 = 15 then
                    match h15 : Evm.step ⟨15, historySevm, s15⟩ with
                    | .halt out =>
                      if commits : Execution.commits out = true then
                        if changed :
                            (Devm.getStor historyPre
                                historySevm.currentTarget).get 0 ≠
                              (Devm.getStor
                                (Execution.committedPost out commits)
                                historySevm.currentTarget).get 0 then
                          if finalValue :
                              (Devm.getStor
                                (Execution.committedPost out commits)
                                historySevm.currentTarget).get 0 = 7 then
                            if stack4 : s4.stack = [0, 5] then
                              if stack9 : s9.stack = [0, 7] then
                                if stack14 : s14.stack = [0, 7] then
                                  some {
                                    s2, s4, s5, s7, s9, s10, s12, s14, s15,
                                    out
                                    h0 := by simpa [hp2] using h0
                                    h2 := by simpa [hp4] using h2
                                    h4 := by simpa [hp5] using h4
                                    h5 := by simpa [hp7] using h5
                                    h7 := by simpa [hp9] using h7
                                    h9 := by simpa [hp10] using h9
                                    h10 := by simpa [hp12] using h10
                                    h12 := by simpa [hp14] using h12
                                    h14 := by simpa [hp15] using h14
                                    h15, commits, changed, finalValue,
                                    stack4, stack9, stack14 }
                                else none else none else none
                          else none
                        else none
                      else none
                    | _ => none
                  else none | _ => none
                else none | _ => none
              else none | _ => none
            else none | _ => none
          else none | _ => none
        else none | _ => none
      else none | _ => none
    else none | _ => none
  else none | _ => none

private def historyAvailable : Bool :=
  historyFixture?.isSome

/-- The selected witness writes final value 7 and is last even though the last
write is a no-op to the value established by the preceding write. -/
private theorem history_lastWriter (fixture : HistoryFixture) :
    ∃ write : Exec.SuccessfulSstoreOccurrence
        fixture.root,
      write.Retained ∧
      write.storageOwner = historySevm.currentTarget ∧
      write.key = 0 ∧ write.value = 7 ∧
      write.occurrence.node.pc = 14 ∧ write.IsLastRetained := by
  rcases fixture.occurrence14.toSuccessfulSstore rfl rfl with
    ⟨write, occurrenceEq⟩
  have retained : write.Retained := by
    unfold Exec.SuccessfulSstoreOccurrence.Retained
    unfold Exec.NinstOccurrence.Retained
    rw [occurrenceEq]
    simp [HistoryFixture.occurrence14, HistoryFixture.root,
      HistoryFixture.run, HistoryFixture.node14, Exec.retainedNodes,
      Exec.retainedNodesOfCommits, fixture.commits]
  have owner : write.storageOwner = historySevm.currentTarget := by
    rw [Exec.SuccessfulSstoreOccurrence.storageOwner, occurrenceEq]
    rfl
  have popped := write.popped
  rw [occurrenceEq] at popped
  change fixture.s14.stack =
    write.key :: write.value :: write.stepPost.stack at popped
  rw [fixture.stack14] at popped
  have key : write.key = 0 := by
    exact Option.some.inj (by simpa using
      (congrArg List.head? popped).symm)
  have value : write.value = 7 := by
    exact Option.some.inj (by simpa using
      (congrArg (fun stack => stack.tail.head?) popped).symm)
  have pc : write.occurrence.node.pc = 14 := by
    rw [occurrenceEq]
    rfl
  refine ⟨write, retained, owner, key, value, pc, ?_⟩
  unfold Exec.SuccessfulSstoreOccurrence.IsLastRetained
  let beforeNodes := (Exec.retainedNodes fixture.run).take 8
  let beforeWrites := beforeNodes.filterMap Exec.Deriv.successfulSstore?
  refine ⟨beforeWrites, [], ?_, by simp⟩
  have nodes : Exec.retainedNodes fixture.run =
      beforeNodes ++ fixture.node14 ::
        [(⟨15, historySevm, fixture.s15, fixture.out,
          .halt fixture.h15⟩ : Exec.Deriv)] := by
    simp [beforeNodes, HistoryFixture.run, HistoryFixture.node14,
      Exec.retainedNodes, Exec.retainedNodesOfCommits, fixture.commits]
  unfold Exec.retainedStorageWrites
  change (Exec.retainedNodes fixture.run).filterMap
    Exec.Deriv.successfulSstore? = beforeWrites ++ [write.storageWrite]
  rw [nodes, List.filterMap_append]
  unfold Exec.SuccessfulSstoreOccurrence.storageWrite
  rw [occurrenceEq, key, value]
  have get14 : Evm.getInst ⟨14, historySevm, fixture.s14⟩ =
      some (.next (.reg .sstore)) := fixture.occurrence14.decoded
  have projected14 : fixture.node14.successfulSstore? = some {
      node := fixture.node14
      owner := historySevm.currentTarget
      key := 0
      value := 7 } := by
    simp [Exec.Deriv.successfulSstore?, HistoryFixture.node14,
      get14, fixture.stack14]
  have suffix : [fixture.node14,
      (⟨15, historySevm, fixture.s15, fixture.out,
        .halt fixture.h15⟩ : Exec.Deriv)].filterMap
          Exec.Deriv.successfulSstore? = [{
      node := fixture.node14
      owner := historySevm.currentTarget
      key := 0
      value := 7 }] := by
    simp only [List.filterMap_cons, List.filterMap_nil, projected14]
    simp [Exec.Deriv.successfulSstore?]
  rw [suffix]
  simp [beforeWrites, HistoryFixture.occurrence14,
    HistoryFixture.node14]

/-- The same concrete history also instantiates the public changed-cell
last-writer theorem; the explicit theorem above identifies its maximal event
as the final no-op SSTORE at PC 14. -/
private theorem history_publicLastWriter (fixture : HistoryFixture) :
    ∃ write : Exec.SuccessfulSstoreOccurrence fixture.root,
      write.Retained ∧
      write.storageOwner = historySevm.currentTarget ∧
      write.key = 0 ∧ write.value = 7 ∧ write.IsLastRetained := by
  rcases Exec.exists_lastRetainedSstore_of_getStor_ne
      fixture.run fixture.commits fixture.changed with
    ⟨write, retained, owner, key, value, last⟩
  exact ⟨write, retained, owner, key, value.trans fixture.finalValue, last⟩

/-! Compiler/source controls. -/

private def payloadProgram : Prog :=
  ⟨.next (.push [0x55] (by decide)) (.last .stop), []⟩

private def payloadContains55 : Bool :=
  match payloadProgram.compile with
  | some bytes => bytes.contains 0x55
  | none => false

private def payloadHasSourceSstore : Bool :=
  payloadProgram.sourceSites.any fun site =>
    match site.instruction with
    | .reg .sstore => true
    | _ => false

/-- Source enumeration rejects the `0x55` PUSH payload despite the raw byte. -/
private theorem payload_not_source_sstore : payloadHasSourceSstore = false := by
  decide

/-- One actual compiled source SSTORE, preceded only by the compiler's entry
`JUMPDEST`, so its exact structural source path is at PC 1. -/
private def sourceProgram : Prog :=
  ⟨.next (.reg .sstore) (.last .stop), []⟩

private def sourceAddress : Adr := 0x200
private def otherSourceAddress : Adr := 0x201
private def otherStorageTarget : Adr := 0x202
private def sourceCode : ByteArray := ByteArray.mk #[0x5b, 0x55, 0x00]
private def sourceSevm : Sevm :=
  { (default : Sevm) with
    code := sourceCode
    codeAddress := some sourceAddress }
private def sourcePre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [0, 1]

private structure SourceFixture where
  afterJump : Devm
  afterStore : Devm
  out : Execution
  step0 : Evm.step ⟨0, sourceSevm, sourcePre⟩ = .cont 1 afterJump
  step1 : Evm.step ⟨1, sourceSevm, afterJump⟩ = .cont 2 afterStore
  tail : Exec 2 sourceSevm afterStore out
  commits : Execution.commits out = true
  compiled : some sourceCode.toList = sourceProgram.compile

private def SourceFixture.run (w : SourceFixture) :
    Exec 0 sourceSevm sourcePre w.out :=
  .cont w.step0 (.cont w.step1 w.tail)

private def SourceFixture.frame (w : SourceFixture) : Exec.Frame :=
  ⟨0, sourceSevm, sourcePre, w.out, w.run, w.commits⟩

private def SourceFixture.node (w : SourceFixture) : Exec.Deriv :=
  ⟨1, sourceSevm, w.afterJump, w.out, .cont w.step1 w.tail⟩

private def SourceFixture.occurrence (w : SourceFixture) :
    Exec.NinstOccurrence w.frame.rootDeriv :=
  { node := w.node
    instruction := .reg .sstore
    slot := .none
    stepResult := .ok w.afterStore
    reached := by
      simp [SourceFixture.frame, SourceFixture.run,
        SourceFixture.node, Exec.Frame.rootDeriv, Exec.rawNodes]
    decoded := by
      change Ninst.At sourceSevm.code 1 (.reg .sstore)
      rfl
    filled := trivial
    stepRun := by
      change Ninst.StepRun 1 sourceSevm w.afterJump (.reg .sstore)
        .none (.ok w.afterStore)
      unfold Ninst.StepRun
      rw [← Evm.step_next
        (show Ninst.At sourceSevm.code 1 (.reg .sstore) by rfl),
        w.step1]
      exact ⟨rfl, rfl⟩ }

private def sourceFixture? : Option SourceFixture :=
  if compiled : some sourceCode.toList = sourceProgram.compile then
    match step0 : Evm.step ⟨0, sourceSevm, sourcePre⟩ with
    | .cont pc1 afterJump =>
      if hpc1 : pc1 = 1 then
        match step1 : Evm.step ⟨1, sourceSevm, afterJump⟩ with
        | .cont pc2 afterStore =>
          if hpc2 : pc2 = 2 then
            let out := exec ⟨2, sourceSevm, afterStore⟩
            if commits : Execution.commits out = true then
              let tail : Exec 2 sourceSevm afterStore out :=
                Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
              some {
                afterJump
                afterStore
                out
                step0 := by simpa [hpc1] using step0
                step1 := by simpa [hpc2] using step1
                tail
                commits
                compiled }
            else none
          else none
        | _ => none
      else none
    | _ => none
  else none

private def exactSourceSite : Bool :=
  match sourceProgram.sourceSiteAt 1 with
  | some site =>
      site.path == (⟨0, []⟩ : Prog.SourcePath) &&
        site.pc == 1 &&
          match site.instruction with
          | .reg .sstore => true
          | _ => false
  | none => false

private def sourceFixtureAvailable : Bool :=
  match sourceProgram.compile with
  | some bytes => if bytes = sourceCode.toList then
      match Evm.step ⟨0, sourceSevm, sourcePre⟩ with
      | .cont pc1 afterJump => pc1 == 1 &&
          match Evm.step ⟨1, sourceSevm, afterJump⟩ with
          | .cont pc2 afterStore => pc2 == 2 &&
              Execution.commits (exec ⟨2, sourceSevm, afterStore⟩)
          | _ => false
      | _ => false
    else false
  | none => false

private theorem sourceFixture_nonempty : Nonempty SourceFixture := by
  have available : sourceFixtureAvailable = true := by
    native_decide
  have hsome : sourceFixture?.isSome = true := by
    unfold sourceFixture? sourceFixtureAvailable at *
    repeat' split
    all_goals grind
  cases fixture : sourceFixture? with
  | none => simp [fixture] at hsome
  | some witness => exact ⟨witness⟩

private theorem SourceFixture.exact (w : SourceFixture) :
    w.frame.exactInvocation sourceProgram
      sourceSevm.currentTarget sourceAddress :=
  ⟨rfl, rfl, rfl, w.compiled⟩

private theorem SourceFixture.source_and_identity_controls
    (w : SourceFixture) :
    (∃ write : Exec.SuccessfulSstoreOccurrence w.frame.rootDeriv,
      write.occurrence.node.pc = 1 ∧
        sourceProgram.acceptsSstoreSite ⟨0, []⟩
          write.occurrence.node.pc = true) ∧
    w.frame.exactInvocation sourceProgram
      sourceSevm.currentTarget sourceAddress ∧
    ¬ w.frame.exactInvocation sourceProgram
      otherStorageTarget sourceAddress ∧
    ¬ w.frame.exactInvocation sourceProgram
      sourceSevm.currentTarget otherSourceAddress := by
  rcases w.occurrence.toSuccessfulSstore rfl rfl with ⟨write, occurrenceEq⟩
  refine ⟨⟨write, ?_, ?_⟩, w.exact, ?_, ?_⟩
  · rw [occurrenceEq]
    rfl
  · rw [occurrenceEq]
    change sourceProgram.acceptsSstoreSite ⟨0, []⟩ 1 = true
    decide
  · intro drifted
    exact (by decide : otherStorageTarget ≠ sourceSevm.currentTarget)
      (drifted.2.1.symm.trans w.exact.2.1)
  · intro drifted
    exact (by decide : otherSourceAddress ≠ sourceAddress)
      (Option.some.inj (drifted.2.2.1.symm.trans w.exact.2.2.1))

/-- The evaluator's exact `sourceFixture?` builder supplies the proof-indexed
compiled SSTORE and exact-identity control, rather than merely mirroring its
field tests in a disconnected Boolean. -/
private theorem concrete_source_and_identity_controls :
    ∃ w : SourceFixture,
      (∃ write : Exec.SuccessfulSstoreOccurrence w.frame.rootDeriv,
        write.occurrence.node.pc = 1 ∧
          sourceProgram.acceptsSstoreSite ⟨0, []⟩
            write.occurrence.node.pc = true) ∧
      w.frame.exactInvocation sourceProgram
        sourceSevm.currentTarget sourceAddress ∧
      ¬ w.frame.exactInvocation sourceProgram
        otherStorageTarget sourceAddress ∧
      ¬ w.frame.exactInvocation sourceProgram
        sourceSevm.currentTarget otherSourceAddress := by
  rcases sourceFixture_nonempty with ⟨w⟩
  exact ⟨w, w.source_and_identity_controls⟩

/-! Exact invocation identity controls. -/

private theorem exactInvocation_rejects_identity_drift
    {frame : Exec.Frame} {program : Prog} {storage codeAddress : Adr}
    (exact : frame.exactInvocation program storage codeAddress) :
    (∀ other, other ≠ storage →
      ¬ frame.exactInvocation program other codeAddress) ∧
    (∀ other, other ≠ codeAddress →
      ¬ frame.exactInvocation program storage other) := by
  constructor
  · intro other different weakened
    exact different (weakened.2.1.symm.trans exact.2.1)
  · intro other different weakened
    exact different (Option.some.inj
      (weakened.2.2.1.symm.trans exact.2.2.1))

/-! Spawn controls use actual CALL execution branches. -/

private def callTarget : Adr := 0x100
private def callParentCode : ByteArray := ByteArray.mk #[0xf1, 0x00]
private def committedChildCode : ByteArray := ByteArray.mk #[0x00]
private def failedChildCode : ByteArray :=
  ByteArray.mk #[0x60,0,0x60,0,0xfd]
private def callSevm : Sevm :=
  { (default : Sevm) with code := callParentCode }
private def callPre (childCode : ByteArray) : Devm :=
  let pre := ((default : Devm).withGasLeft 100000).withStack
    [10000, callTarget.toB256, 0, 0, 0, 0, 0]
  pre.withState (pre.state.setCode callTarget childCode)
private def callEvm (childCode : ByteArray) : Evm :=
  ⟨0, callSevm, callPre childCode⟩

private structure CallFixture where
  childCode : ByteArray
  nextPc : Nat
  resumed : Devm
  frame : Jaune.Frame
  resume : Resume
  childEvm : Evm
  raw : Execution
  out : Execution
  hstep : (callEvm childCode).step = .spawn frame resume nextPc
  henter : frame.enter = .run childEvm
  child : Exec childEvm.pc childEvm.sta childEvm.dyna raw
  hresume : resume.run (frame.settle raw) = .ok resumed
  next : Exec nextPc callSevm resumed out
  rootCommits : Execution.commits out = true

private def CallFixture.run (w : CallFixture) :
    Exec 0 callSevm (callPre w.childCode) w.out :=
  .runOk w.hstep w.henter w.child w.hresume w.next

private def CallFixture.root (w : CallFixture) : Exec.Deriv :=
  ⟨0, callSevm, callPre w.childCode, w.out, w.run⟩

private theorem CallFixture.raw_order (w : CallFixture) :
    Exec.rawNodes w.run =
      w.root :: (Exec.rawNodes w.child ++ Exec.rawNodes w.next) := by
  simp [CallFixture.run, CallFixture.root, Exec.rawNodes]

private theorem CallFixture.retained_order_of_settles
    (w : CallFixture)
    (settles : Frame.settlementCommits w.frame w.raw = true) :
    Exec.retainedNodes w.run =
      w.root :: (Exec.retainedNodes w.child ++ Exec.retainedNodes w.next) := by
  simpa [CallFixture.run, CallFixture.root] using
    Exec.retainedNodes_runOk_of_settlementCommits
      w.hstep w.henter w.child w.hresume w.next w.rootCommits settles

private theorem CallFixture.retained_prunes_of_not_settles
    (w : CallFixture)
    (notSettles : Frame.settlementCommits w.frame w.raw ≠ true) :
    Exec.retainedNodes w.run = w.root :: Exec.retainedNodes w.next := by
  simpa [CallFixture.run, CallFixture.root] using
    Exec.retainedNodes_runOk_of_not_settlementCommits
      w.hstep w.henter w.child w.hresume w.next w.rootCommits notSettles

private def callFixture? (childCode : ByteArray) : Option CallFixture :=
  match hstep : (callEvm childCode).step with
  | .spawn frame resume nextPc =>
      match henter : frame.enter with
      | .run childEvm =>
          let raw := exec childEvm
          match hresume : resume.run (frame.settle raw) with
          | .ok resumed =>
              let out := exec ⟨nextPc, callSevm, resumed⟩
              if rootCommits : Execution.commits out = true then
                let child := Classical.choice
                  ((exec_iff_exec_eq _ _ _ _).2 rfl)
                let next := Classical.choice
                  ((exec_iff_exec_eq _ _ _ _).2 rfl)
                some {
                  childCode := childCode
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
                  rootCommits := rootCommits }
              else none
          | .error _ => none
      | .done _ => none
  | _ => none

private structure CommittedCallFixture where
  call : CallFixture
  childCode_eq : call.childCode = committedChildCode
  settles : Frame.settlementCommits call.frame call.raw = true

private structure CaughtCallFixture where
  call : CallFixture
  childCode_eq : call.childCode = failedChildCode
  rawDoesNotCommit : Execution.commits call.raw ≠ true
  doesNotSettle : Frame.settlementCommits call.frame call.raw ≠ true

private def committedCallFixture? : Option CommittedCallFixture :=
  match callFixture? committedChildCode with
  | some call =>
      if childCode_eq : call.childCode = committedChildCode then
        if settles : Frame.settlementCommits call.frame call.raw = true then
          some ⟨call, childCode_eq, settles⟩
        else none
      else none
  | none => none

private def caughtCallFixture? : Option CaughtCallFixture :=
  match callFixture? failedChildCode with
  | some call =>
      if childCode_eq : call.childCode = failedChildCode then
        if rawDoesNotCommit : Execution.commits call.raw ≠ true then
          if doesNotSettle :
              Frame.settlementCommits call.frame call.raw ≠ true then
            some ⟨call, childCode_eq, rawDoesNotCommit, doesNotSettle⟩
          else none
        else none
      else none
  | none => none

private theorem committedCall_order (w : CommittedCallFixture) :
    Exec.rawNodes w.call.run = w.call.root ::
        (Exec.rawNodes w.call.child ++ Exec.rawNodes w.call.next) ∧
      Exec.retainedNodes w.call.run = w.call.root ::
        (Exec.retainedNodes w.call.child ++ Exec.retainedNodes w.call.next) :=
  ⟨w.call.raw_order, w.call.retained_order_of_settles w.settles⟩

private theorem caughtCall_raw_but_pruned (w : CaughtCallFixture) :
    Exec.rawNodes w.call.run = w.call.root ::
        (Exec.rawNodes w.call.child ++ Exec.rawNodes w.call.next) ∧
      Exec.retainedNodes w.call.run =
        w.call.root :: Exec.retainedNodes w.call.next :=
  ⟨w.call.raw_order, w.call.retained_prunes_of_not_settles w.doesNotSettle⟩

private def committedChildAvailable : Bool :=
  match (callEvm committedChildCode).step with
  | .spawn frame resume nextPc =>
      match frame.enter with
      | .run childEvm =>
          let raw := exec childEvm
          Frame.settlementCommits frame raw &&
            match resume.run (frame.settle raw) with
            | .ok resumed =>
                Execution.commits (exec ⟨nextPc, callSevm, resumed⟩)
            | .error _ => false
      | .done _ => false
  | _ => false

private def caughtFailedChildAvailable : Bool :=
  match (callEvm failedChildCode).step with
  | .spawn frame resume nextPc =>
      match frame.enter with
      | .run childEvm =>
          let raw := exec childEvm
          !Execution.commits raw && !Frame.settlementCommits frame raw &&
            match resume.run (frame.settle raw) with
            | .ok resumed =>
                Execution.commits (exec ⟨nextPc, callSevm, resumed⟩)
            | .error _ => false
      | .done _ => false
  | _ => false

private theorem committedCallFixture_nonempty : Nonempty CommittedCallFixture := by
  have available : committedChildAvailable = true := by
    native_decide
  have hsome : committedCallFixture?.isSome = true := by
    unfold committedCallFixture? callFixture? committedChildAvailable at *
    repeat' split
    all_goals grind
  cases fixture : committedCallFixture? with
  | none => simp [fixture] at hsome
  | some witness => exact ⟨witness⟩

private theorem caughtCallFixture_nonempty : Nonempty CaughtCallFixture := by
  have available : caughtFailedChildAvailable = true := by
    native_decide
  have hsome : caughtCallFixture?.isSome = true := by
    unfold caughtCallFixture? callFixture? caughtFailedChildAvailable at *
    repeat' split
    all_goals grind
  cases fixture : caughtCallFixture? with
  | none => simp [fixture] at hsome
  | some witness => exact ⟨witness⟩

/-- Both exact option builders are inhabited and feed the proof-indexed raw
and retained chronology equations used by this gate. -/
private theorem concreteCall_orders :
    (∃ w : CommittedCallFixture,
      Exec.rawNodes w.call.run = w.call.root ::
          (Exec.rawNodes w.call.child ++ Exec.rawNodes w.call.next) ∧
        Exec.retainedNodes w.call.run = w.call.root ::
          (Exec.retainedNodes w.call.child ++ Exec.retainedNodes w.call.next)) ∧
    (∃ w : CaughtCallFixture,
      Exec.rawNodes w.call.run = w.call.root ::
          (Exec.rawNodes w.call.child ++ Exec.rawNodes w.call.next) ∧
        Exec.retainedNodes w.call.run =
          w.call.root :: Exec.retainedNodes w.call.next) := by
  rcases committedCallFixture_nonempty with ⟨committed⟩
  rcases caughtCallFixture_nonempty with ⟨caught⟩
  exact ⟨⟨committed, committedCall_order committed⟩,
    ⟨caught, caughtCall_raw_but_pruned caught⟩⟩

-- The gate requires this exact evaluator vector.
#eval! [
  terminalFixture?.isSome,
  rootSstoreAvailable noOpSevm noOpPre,
  rootSstoreAvailable revertSevm revertPre,
  decide (Execution.commits (exec ⟨0, revertSevm, revertPre⟩) ≠ true),
  rootSstoreAvailable laterOogSevm laterOogPre,
  decide (Execution.commits (exec ⟨0, laterOogSevm, laterOogPre⟩) ≠ true),
  committedChildAvailable,
  caughtFailedChildAvailable,
  payloadContains55,
  !payloadHasSourceSstore,
  historyAvailable,
  sourceFixtureAvailable,
  exactSourceSite]

-- TERMINAL-ERROR-MUTANT-CONTROL
-- RAW-ERROR-PRUNE-MUTANT-CONTROL
-- RAW-BYTE-SCAN-MUTANT-CONTROL
-- FIRST-WRITER-MUTANT-CONTROL
-- IDENTITY-MUTANT-CONTROL
-- CODE-IDENTITY-MUTANT-CONTROL
-- WETH-BRIDGE-MUTANT-CONTROL

end

end Blanc.ExecutionOccurrenceRegression
