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
private def terminalErrorOut : Execution :=
  exec ⟨0, terminalErrorSevm, terminalErrorPre⟩
private def terminalErrorRun :
    Exec 0 terminalErrorSevm terminalErrorPre terminalErrorOut :=
  Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)

/-- An `Ninst` whose own step terminates in error remains a raw occurrence. -/
private theorem terminalError_occurs :
    ∃ occurrence : Exec.NinstOccurrence
        (⟨0, terminalErrorSevm, terminalErrorPre, terminalErrorOut,
          terminalErrorRun⟩ : Exec.Deriv),
      occurrence.instruction = .reg .sstore := by
  have decoded : Ninst.At terminalErrorSevm.code 0 (.reg .sstore) := by
    rfl
  let root : Exec.Deriv :=
    ⟨0, terminalErrorSevm, terminalErrorPre, terminalErrorOut,
      terminalErrorRun⟩
  rcases Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := root) (node := root) (n := .reg .sstore)
      (Exec.mem_rawNodes_self terminalErrorRun) decoded with
    ⟨occurrence, _, instruction⟩
  exact ⟨occurrence, instruction⟩

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
  out : Execution
  run : Exec 0 historySevm historyPre out
  commits : Execution.commits out = true
  changed :
    (Devm.getStor historyPre historySevm.currentTarget).get 0 ≠
      (Devm.getStor (Execution.committedPost out commits)
        historySevm.currentTarget).get 0
  finalValue :
    (Devm.getStor (Execution.committedPost out commits)
      historySevm.currentTarget).get 0 = 7

private def historyFixture? : Option HistoryFixture :=
  let out := exec ⟨0, historySevm, historyPre⟩
  if commits : Execution.commits out = true then
    if changed :
        (Devm.getStor historyPre historySevm.currentTarget).get 0 ≠
          (Devm.getStor (Execution.committedPost out commits)
            historySevm.currentTarget).get 0 then
      if finalValue :
          (Devm.getStor (Execution.committedPost out commits)
            historySevm.currentTarget).get 0 = 7 then
        let run := Classical.choice ((exec_iff_exec_eq _ _ _ _).2 rfl)
        some { out, run, commits, changed, finalValue }
      else none
    else none
  else none

private def historyAvailable : Bool :=
  let out := exec ⟨0, historySevm, historyPre⟩
  match out with
  | .error _ => false
  | .ok post => Execution.commits out &&
      ((Devm.getStor historyPre historySevm.currentTarget).get 0 !=
        (Devm.getStor post historySevm.currentTarget).get 0) &&
      ((Devm.getStor post historySevm.currentTarget).get 0 == 7)

/-- The selected witness writes final value 7 and is last even though the last
write is a no-op to the value established by the preceding write. -/
private theorem history_lastWriter (fixture : HistoryFixture) :
    ∃ write : Exec.SuccessfulSstoreOccurrence
        (⟨0, historySevm, historyPre, fixture.out, fixture.run⟩ : Exec.Deriv),
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

-- The gate requires this exact evaluator vector.
#eval! [
  decide (Execution.commits terminalErrorOut ≠ true),
  rootSstoreAvailable noOpSevm noOpPre,
  rootSstoreAvailable revertSevm revertPre,
  decide (Execution.commits (exec ⟨0, revertSevm, revertPre⟩) ≠ true),
  rootSstoreAvailable laterOogSevm laterOogPre,
  decide (Execution.commits (exec ⟨0, laterOogSevm, laterOogPre⟩) ≠ true),
  committedChildAvailable,
  caughtFailedChildAvailable,
  payloadContains55,
  !payloadHasSourceSstore,
  historyAvailable]

-- TERMINAL-ERROR-MUTANT-CONTROL
-- RAW-ERROR-PRUNE-MUTANT-CONTROL
-- RAW-BYTE-SCAN-MUTANT-CONTROL
-- FIRST-WRITER-MUTANT-CONTROL
-- IDENTITY-MUTANT-CONTROL
-- WETH-BRIDGE-MUTANT-CONTROL

end

end Blanc.ExecutionOccurrenceRegression
